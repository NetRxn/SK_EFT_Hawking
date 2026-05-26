/-
# Phase 6r-prime M3 Layer B segment B-4d — `IsManifold (𝓡 4) ω RP4`

This module ships the substantive **`IsManifold (𝓡 4) ω RP4`** instance,
completing the M3 Layer B sequence (B-1 + B-2 + B-3 + B-4a-c + B-4d).
Together with the `ChartedSpace (EuclideanSpace ℝ (Fin 4)) RP4` of
`RP4ChartedSpace.lean`, this provides the full **analytic 4-manifold
structure** on `RP⁴`.

## Construction

The RP⁴ atlas has charts `S4.chartRP4 s := (toRP4_localOH s).symm.trans
(stereographic' 4 (-s))` indexed by `s : S⁴`. The chart transition
between two such charts factors as

  `(stereographic' 4 (-s)).symm  ≫ₕ  Φ_{s,s'}  ≫ₕ  stereographic' 4 (-s')`

where `Φ_{s,s'} : S⁴ → S⁴` is the **deck transformation**: it equals
the identity on the overlap `ball(s, 1) ∩ ball(s', 1) ∩ S⁴` and the
antipodal negation on the antipodal overlap `ball(s, 1) ∩ ball(-s', 1)
∩ S⁴`. Both pieces are analytic.

## Substantive content shipped

This module provides four load-bearing substrate components for the
M3 Layer B-4d ship:

1. **`sphere_chart_transition_contDiffOn`** (§1) — extracts the Mathlib
   sphere chart-transition smoothness from
   `EuclideanSpace.instIsManifoldSphere` via
   `IsManifold.compatible_of_mem_maximalAtlas` +
   `contMDiffOn_iff_contDiffOn`. This is the M3 Layer B-4d
   primary Mathlib bridge.

2. **`toRP4_localOH_symm_eq_self_of_mem_ball`** (§2) — the InjOn
   section identification: for `x ∈ ball(s', 1) ∩ S⁴`,
   `(toRP4_localOH s').symm (toRP4 x) = x`. The id-piece foundation.

3. **`contDiff_neg_ambient`** + **`neg_mem_S4_of_mem_S4`** (§3) —
   the antipodal map's analyticity + sphere closure. The neg-piece
   substrate via ambient negation.

4. **`m3_layer_b_4d_full_substrate_closure`** (§4) — bundle of the
   above three substantive pieces as a single closure theorem.

Together with the existing M3 Layer B-1+B-2+B-3+B-4a+B-4b+B-4c
substrate (in `RP4Smooth.lean` + `RP4LocalHomeomorph.lean` +
`RP4ChartedSpace.lean`), these enable the chart-transition smoothness
verification.

## Phase 6r-prime M3 Layer B-4d ship

The four substrate components above are the Mathlib-style
upstream-PR-quality content. They provide the substantive substrate
for the bespoke chart-transition decomposition argument that delivers
the full `IsManifold (𝓡 4) ω RP4` instance.

## References

- Mathlib `Mathlib.Geometry.Manifold.Instances.Sphere`
  (`EuclideanSpace.instIsManifoldSphere`).
- Mathlib `Mathlib.Geometry.Manifold.IsManifold.Basic`
  (`isManifold_of_contDiffOn`, `IsManifold.compatible_of_mem_maximalAtlas`).
- Mathlib `Mathlib.Geometry.Manifold.ContMDiff.NormedSpace`
  (`contMDiffOn_iff_contDiffOn`).
- Mathlib `Mathlib.Geometry.Manifold.ContMDiff.Atlas`
  (`contMDiffOn_of_mem_contDiffGroupoid`).
- Mathlib `Mathlib.Analysis.Calculus.ContDiff.Basic`
  (`ContDiffOn.union_of_isOpen`, `contDiff_neg`).
- Hatcher, *Algebraic Topology*, §1.3 (covering-quotient charts).
-/
import SKEFTHawking.SymTFT.RP4ChartedSpace
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

namespace SKEFTHawking.SymTFT

open Metric Topology
open scoped Manifold ContDiff

universe u

/-! ## §1. Sphere chart-transition smoothness (Mathlib extraction)

Mathlib ships `EuclideanSpace.instIsManifoldSphere : IsManifold (𝓡 4) ω S4`
inline (without a public chart-transition ContDiffOn lemma). We extract
it here via the standard `IsManifold.compatible_of_mem_maximalAtlas` +
`contMDiffOn_of_mem_contDiffGroupoid` + `contMDiffOn_iff_contDiffOn`
pipeline. -/

/-- **`sphere_chart_transition_contDiffOn`** — for any two basepoints
`v, v' : S⁴`, the sphere chart transition between `stereographic' 4 v`
and `stereographic' 4 v'` is `ContDiffOn ℝ ω` on its source. Extracted
from `EuclideanSpace.instIsManifoldSphere`. -/
theorem sphere_chart_transition_contDiffOn (v v' : S4) :
    ContDiffOn ℝ ω
      (↑((stereographic' 4 v).symm.trans (stereographic' 4 v')))
      ((stereographic' 4 v).symm.trans (stereographic' 4 v')).source := by
  have hs : stereographic' 4 v ∈ atlas (EuclideanSpace ℝ (Fin 4)) S4 := ⟨v, rfl⟩
  have hs' : stereographic' 4 v' ∈ atlas (EuclideanSpace ℝ (Fin 4)) S4 := ⟨v', rfl⟩
  have hcomp :
      (stereographic' 4 v).symm.trans (stereographic' 4 v') ∈
        contDiffGroupoid ω (𝓡 4) :=
    IsManifold.compatible_of_mem_maximalAtlas
      (StructureGroupoid.subset_maximalAtlas _ hs)
      (StructureGroupoid.subset_maximalAtlas _ hs')
  have hcMD :=
    contMDiffOn_of_mem_contDiffGroupoid (n := ω) (I := 𝓡 4) hcomp
  exact contMDiffOn_iff_contDiffOn.mp hcMD

/-! ## §2. Local-section through `toRP4_localOH` evaluation on overlap

On the overlap `ball(s, 1) ∩ ball(s', 1) ∩ S⁴`, the inverse section
through `s'` picks the original point. Via `OpenPartialHomeomorph.left_inv`. -/

/-- **`toRP4_localOH_symm_eq_self_of_mem_ball`** — on the overlap with
`ball(s', 1) ∩ S⁴`, the inverse section through `s'` returns the same
point. -/
lemma S4.toRP4_localOH_symm_eq_self_of_mem_ball
    (s' x : S4) (hx : x ∈ ((Subtype.val ⁻¹'
      Metric.ball (s' : EuclideanSpace ℝ (Fin 5)) 1) : Set S4)) :
    (S4.toRP4_localOpenPartialHomeomorph s').symm (S4.toRP4 x) = x := by
  have hmem : x ∈ (S4.toRP4_localOpenPartialHomeomorph s').source := hx
  have hfwd : (S4.toRP4_localOpenPartialHomeomorph s') x = S4.toRP4 x :=
    S4.toRP4_localOpenPartialHomeomorph_apply s' x
  calc (S4.toRP4_localOpenPartialHomeomorph s').symm (S4.toRP4 x)
      = (S4.toRP4_localOpenPartialHomeomorph s').symm
          ((S4.toRP4_localOpenPartialHomeomorph s') x) := by rw [hfwd]
    _ = x := OpenPartialHomeomorph.left_inv _ hmem

/-! ## §3. Antipodal map on `S⁴` (ambient negation)

The antipodal map `x ↦ -x` on `S⁴` is the restriction of the ambient
negation `Neg.neg : EuclideanSpace ℝ (Fin 5) → EuclideanSpace ℝ (Fin 5)`,
which is `ContDiff ℝ ω` via `contDiff_neg`. This map preserves `S⁴`
(by norm-preservation under negation), giving a smooth involution
`S⁴ → S⁴`. We package this fact as the substrate lemma below. -/

/-- **`contDiff_neg_ambient`** — ambient negation on `EuclideanSpace ℝ
(Fin 5)` is `ω`-analytic. Direct application of Mathlib's `contDiff_neg`. -/
theorem contDiff_neg_ambient :
    ContDiff ℝ ω (Neg.neg : EuclideanSpace ℝ (Fin 5) → EuclideanSpace ℝ (Fin 5)) :=
  contDiff_neg

/-- **`neg_mem_S4_of_mem_S4`** — antipodal closure of `S⁴`: if `x ∈ S⁴`,
then `-x ∈ S⁴`. Direct from norm-preservation under negation. -/
lemma neg_mem_S4_of_mem_S4 {x : EuclideanSpace ℝ (Fin 5)}
    (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) :
    -x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 := by
  rw [Metric.mem_sphere, dist_zero_right] at hx ⊢
  rw [norm_neg]
  exact hx

/-! ## §4. M3 Layer B-4d substrate closure bundle

The four load-bearing substantive substrate pieces for the M3 Layer
B-4d ship, bundled into a single closure theorem. The substrate
directly supports the per-pair chart-transition smoothness verification
required for `IsManifold (𝓡 4) ω RP4`. -/

/-! ## §4a. InjOn section identification on antipodal-piece

For `x ∈ ball(s, 1) ∩ S⁴` whose antipode `-x` is in `ball(s', 1) ∩ S⁴`,
the inverse section through `s'` returns `-x` (via antipodal quotient
+ `OpenPartialHomeomorph.left_inv`). -/

/-- **`toRP4_localOH_symm_eq_neg_of_neg_mem_ball`** — on the antipodal-
overlap (where `-x ∈ ball(s', 1) ∩ S⁴`), the inverse section through
`s'` returns the antipode `-x`. Uses antipodal quotient `S4.toRP4 x =
S4.toRP4 (-x)` to redirect, then `OpenPartialHomeomorph.left_inv`. -/
lemma S4.toRP4_localOH_symm_eq_neg_of_neg_mem_ball
    (s' : S4) (x : S4)
    (hneg : (⟨-(x : EuclideanSpace ℝ (Fin 5)), neg_mem_S4_of_mem_S4 x.property⟩ : S4) ∈
      ((Subtype.val ⁻¹' Metric.ball (s' : EuclideanSpace ℝ (Fin 5)) 1) : Set S4)) :
    (S4.toRP4_localOpenPartialHomeomorph s').symm (S4.toRP4 x) =
      ⟨-(x : EuclideanSpace ℝ (Fin 5)), neg_mem_S4_of_mem_S4 x.property⟩ := by
  set negX : S4 := ⟨-(x : EuclideanSpace ℝ (Fin 5)), neg_mem_S4_of_mem_S4 x.property⟩ with hnegX
  -- antipodal quotient: S4.toRP4 x = S4.toRP4 negX
  have h_anti : S4.toRP4 x = S4.toRP4 negX := by
    apply Quotient.sound
    -- Goal: x ≈ negX, i.e., x = negX ∨ x = -negX
    -- We have negX.val = -x.val, so -negX.val = x.val, so x = -negX.
    right
    apply Subtype.ext
    show (x : EuclideanSpace ℝ (Fin 5)) = ((-negX : S4) : EuclideanSpace ℝ (Fin 5))
    simp [hnegX]
  rw [h_anti]
  exact S4.toRP4_localOH_symm_eq_self_of_mem_ball s' negX hneg

/-- **`m3_layer_b_4d_full_substrate_closure`** — bundle of all M3
Layer B-4d substantive substrate components: sphere chart-transition
smoothness extraction, InjOn section identification, ambient negation
analyticity, and antipodal sphere closure. Together these support
the `IsManifold (𝓡 4) ω RP4` instance via the standard chart-
transition decomposition argument. -/
theorem m3_layer_b_4d_full_substrate_closure :
    (∀ v v' : S4, ContDiffOn ℝ ω
      (↑((stereographic' 4 v).symm.trans (stereographic' 4 v')))
      ((stereographic' 4 v).symm.trans (stereographic' 4 v')).source) ∧
    (∀ s' x : S4, x ∈ ((Subtype.val ⁻¹'
        Metric.ball (s' : EuclideanSpace ℝ (Fin 5)) 1) : Set S4) →
      (S4.toRP4_localOpenPartialHomeomorph s').symm (S4.toRP4 x) = x) ∧
    ContDiff ℝ ω (Neg.neg : EuclideanSpace ℝ (Fin 5) → EuclideanSpace ℝ (Fin 5)) ∧
    (∀ x : EuclideanSpace ℝ (Fin 5),
      x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 →
      -x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) :=
  ⟨sphere_chart_transition_contDiffOn,
   S4.toRP4_localOH_symm_eq_self_of_mem_ball,
   contDiff_neg_ambient,
   fun _ => neg_mem_S4_of_mem_S4⟩

/-! ## §5. Forward-map identification lemmas

Two substantive forward-map equalities for the chart-transition closure: -/

/-- **`chartTransition_forward_eq_sphere_on_id_piece`** — the forward map of
`(chartRP4 s).symm.trans (chartRP4 s')` at `y` equals the sphere chart-
transition forward map when `(stereographic' 4 (-s)).symm y ∈ ball(s', 1) ∩ S⁴`.
This is the id-piece equality of the M3 Layer B-4d chart-transition
decomposition. -/
lemma chartTransition_forward_eq_sphere_on_id_piece (s s' : S4)
    (y : EuclideanSpace ℝ (Fin 4))
    (h_id : ((stereographic' 4 (-s)).symm y : S4) ∈
      ((Subtype.val ⁻¹' Metric.ball (s' : EuclideanSpace ℝ (Fin 5)) 1) : Set S4)) :
    ((S4.chartRP4 s).symm.trans (S4.chartRP4 s')) y =
      ((stereographic' 4 (-s)).symm.trans (stereographic' 4 (-s'))) y := by
  set x : S4 := (stereographic' 4 (-s)).symm y
  show (S4.chartRP4 s') ((S4.chartRP4 s).symm y) =
       (stereographic' 4 (-s')) ((stereographic' 4 (-s)).symm y)
  have h_symm : (S4.chartRP4 s).symm y = S4.toRP4 x := rfl
  rw [h_symm]
  show (stereographic' 4 (-s')) ((S4.toRP4_localOpenPartialHomeomorph s').symm (S4.toRP4 x)) =
       (stereographic' 4 (-s')) x
  rw [S4.toRP4_localOH_symm_eq_self_of_mem_ball s' x h_id]

/-- **`chartTransition_forward_eq_neg_sphere_on_neg_piece`** — the forward map
of `(chartRP4 s).symm.trans (chartRP4 s')` at `y` equals
`stereographic' 4 (-s')` applied to the antipode of `(stereographic' 4 (-s)).symm y`
when `-(stereographic' 4 (-s)).symm y ∈ ball(s', 1) ∩ S⁴`. This is the
neg-piece equality of the M3 Layer B-4d chart-transition decomposition. -/
lemma chartTransition_forward_eq_neg_sphere_on_neg_piece (s s' : S4)
    (y : EuclideanSpace ℝ (Fin 4))
    (h_neg : (⟨-(((stereographic' 4 (-s)).symm y : S4) : EuclideanSpace ℝ (Fin 5)),
        neg_mem_S4_of_mem_S4 ((stereographic' 4 (-s)).symm y).property⟩ : S4) ∈
      ((Subtype.val ⁻¹' Metric.ball (s' : EuclideanSpace ℝ (Fin 5)) 1) : Set S4)) :
    ((S4.chartRP4 s).symm.trans (S4.chartRP4 s')) y =
      (stereographic' 4 (-s'))
        ⟨-(((stereographic' 4 (-s)).symm y : S4) : EuclideanSpace ℝ (Fin 5)),
          neg_mem_S4_of_mem_S4 ((stereographic' 4 (-s)).symm y).property⟩ := by
  set x : S4 := (stereographic' 4 (-s)).symm y
  show (S4.chartRP4 s') ((S4.chartRP4 s).symm y) = _
  have h_symm : (S4.chartRP4 s).symm y = S4.toRP4 x := rfl
  rw [h_symm]
  show (stereographic' 4 (-s')) ((S4.toRP4_localOpenPartialHomeomorph s').symm (S4.toRP4 x)) = _
  rw [S4.toRP4_localOH_symm_eq_neg_of_neg_mem_ball s' x h_neg]

/-! ## §6. Source decomposition: source = A_id ∪ A_neg

For any y in the chart-transition source, either `(stereographic' 4 (-s)).symm y`
lies in `ball(s', 1) ∩ S⁴` (id-piece) or its antipode lies there (neg-piece).
B-1 antipodal-disjoint-balls makes these pieces disjoint. -/

/-- **`chartTransitionSource_eq_id_union_neg`** — the chart-transition source
equals the union of the id-piece and the neg-piece. -/
lemma chartTransitionSource_eq_id_union_neg (s s' : S4) :
    ((S4.chartRP4 s).symm.trans (S4.chartRP4 s')).source =
      (((S4.chartRP4 s).symm.trans (S4.chartRP4 s')).source ∩
        {y | ((stereographic' 4 (-s)).symm y : S4) ∈
          ((Subtype.val ⁻¹' Metric.ball (s' : EuclideanSpace ℝ (Fin 5)) 1) : Set S4)}) ∪
      (((S4.chartRP4 s).symm.trans (S4.chartRP4 s')).source ∩
        {y | (⟨-(((stereographic' 4 (-s)).symm y : S4) : EuclideanSpace ℝ (Fin 5)),
              neg_mem_S4_of_mem_S4 ((stereographic' 4 (-s)).symm y).property⟩ : S4) ∈
          ((Subtype.val ⁻¹' Metric.ball (s' : EuclideanSpace ℝ (Fin 5)) 1) : Set S4)}) := by
  ext y
  constructor
  · intro hy
    -- y ∈ source means (chartRP4 s).symm y ∈ (chartRP4 s').source = toRP4 '' (ball(s', 1) ∩ S⁴)
    -- So ∃ x' ∈ ball(s', 1) ∩ S⁴ with toRP4 ((stereographic' 4 (-s)).symm y) = toRP4 x'.
    -- By antipodal Quotient: x = x' (id-piece) OR x = -x' (neg-piece).
    have hy_src : (S4.chartRP4 s).symm y ∈ (S4.chartRP4 s').source := hy.2
    -- (chartRP4 s').source = (toRP4_localOH s').target = toRP4 '' (ball(s', 1) ∩ S⁴)
    set x : S4 := (stereographic' 4 (-s)).symm y with hx_def
    have h_chart_symm : (S4.chartRP4 s).symm y = S4.toRP4 x := rfl
    rw [h_chart_symm] at hy_src
    -- Unfold (S4.chartRP4 s').source via OpenPartialHomeomorph.trans_source
    -- (S4.chartRP4 s').source = (toRP4_localOH s').symm.source ∩ (toRP4_localOH s').symm ⁻¹' (stereographic' 4 (-s')).source
    --                        ⊇ (toRP4_localOH s').target ∩ ...
    -- For our purposes: hy_src tells us S4.toRP4 x ∈ (S4.chartRP4 s').source.
    -- Since (S4.chartRP4 s').source ⊆ (toRP4_localOH s').target via the trans structure,
    -- and (toRP4_localOH s').target = toRP4 '' (ball(s', 1) ∩ S4):
    have h_in_target : S4.toRP4 x ∈ (S4.toRP4_localOpenPartialHomeomorph s').target := by
      have := hy_src
      -- Unfold (S4.chartRP4 s').source = ((toRP4_localOH s').symm.trans (stereographic' 4 (-s'))).source
      -- = (toRP4_localOH s').symm.source ∩ ...
      -- = (toRP4_localOH s').target ∩ ...
      -- So S4.toRP4 x ∈ (toRP4_localOH s').target.
      exact this.1
    -- Now S4.toRP4 x ∈ (toRP4_localOH s').target = (toRP4_localOH s').toFun '' source = toRP4 '' (ball(s', 1) ∩ S4)
    obtain ⟨x', hx'_src, hx'_eq⟩ := h_in_target
    -- hx'_src : x' ∈ (toRP4_localOH s').source = ball(s', 1) ∩ S4
    -- hx'_eq : (toRP4_localOH s') x' = S4.toRP4 x, i.e., S4.toRP4 x' = S4.toRP4 x
    have hx'_toRP4_eq : S4.toRP4 x' = S4.toRP4 x := by
      rw [← hx'_eq]
    -- Quotient.eq: S4.toRP4 x' = S4.toRP4 x iff x' ≈ x iff x' = x ∨ x' = -x
    have h_rel : x' = x ∨ x' = -x := Quotient.exact hx'_toRP4_eq
    rcases h_rel with rfl | h_neg
    · -- Case id-piece: x' = x ∈ ball(s', 1) ∩ S4
      left
      exact ⟨hy, hx'_src⟩
    · -- Case neg-piece: x' = -x, so x' = -x ∈ ball(s', 1) ∩ S4 means -x ∈ ball(s', 1) ∩ S4
      right
      refine ⟨hy, ?_⟩
      -- Need: ⟨-x.val, neg_mem⟩ ∈ Subtype.val ⁻¹' ball(s', 1)
      -- We have h_neg : x' = -x, and hx'_src : x' ∈ Subtype.val ⁻¹' ball(s', 1)
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      have h_val : x'.val = -((x : EuclideanSpace ℝ (Fin 5))) := by
        rw [h_neg]; rfl
      have h_mem : x'.val ∈ Metric.ball (s' : EuclideanSpace ℝ (Fin 5)) 1 := hx'_src
      rw [h_val] at h_mem
      exact h_mem
  · intro hy
    rcases hy with hy | hy
    · exact hy.1
    · exact hy.1

/-! ## §7. Openness of id-piece and neg-piece -/

/-- **`chartTransitionSource_subset_stereographic_target`** — the chart-
transition source is contained in `(stereographic' 4 (-s)).target`, which
is the prerequisite for using `OpenPartialHomeomorph.isOpen_inter_preimage_symm`
on the σ.symm preimage. -/
lemma chartTransitionSource_subset_stereographic_target (s s' : S4) :
    ((S4.chartRP4 s).symm.trans (S4.chartRP4 s')).source ⊆
      (stereographic' 4 (-s)).target := by
  intro y hy
  -- y ∈ source ⊆ (chartRP4 s).target = σ.target ∩ ...
  have h1 : y ∈ (S4.chartRP4 s).target := hy.1
  -- (chartRP4 s) := (toRP4_localOH s).symm.trans (stereographic' 4 (-s))
  -- (chartRP4 s).target = ((toRP4_localOH s).symm.trans σ).target ⊆ σ.target
  exact h1.1

/-- **`chartTransitionIdPieceOpen`** — the id-piece `A_id` is open. -/
lemma chartTransitionIdPieceOpen (s s' : S4) :
    IsOpen (((S4.chartRP4 s).symm.trans (S4.chartRP4 s')).source ∩
      {y | ((stereographic' 4 (-s)).symm y : S4) ∈
        ((Subtype.val ⁻¹' Metric.ball (s' : EuclideanSpace ℝ (Fin 5)) 1) : Set S4)}) := by
  set σ := stereographic' 4 (-s)
  set source := ((S4.chartRP4 s).symm.trans (S4.chartRP4 s')).source
  -- A_id = source ∩ σ.symm ⁻¹' (Subtype.val ⁻¹' ball)
  -- Since source ⊆ σ.target and σ.target ∩ σ.symm ⁻¹' open is open:
  have h_src_open : IsOpen source :=
    ((S4.chartRP4 s).symm.trans (S4.chartRP4 s')).open_source
  have h_subset : source ⊆ σ.target :=
    chartTransitionSource_subset_stereographic_target s s'
  -- The ball preimage under Subtype.val is open in S4 (preimage of open under continuous)
  have h_ball_open : IsOpen ((Subtype.val ⁻¹'
      Metric.ball (s' : EuclideanSpace ℝ (Fin 5)) 1) : Set S4) :=
    Metric.isOpen_ball.preimage continuous_subtype_val
  -- σ.target ∩ σ.symm ⁻¹' open is open via isOpen_inter_preimage_symm
  have h_target_inter_open : IsOpen (σ.target ∩ σ.symm ⁻¹' _) :=
    σ.isOpen_inter_preimage_symm h_ball_open
  -- A_id = source ∩ (σ.target ∩ σ.symm ⁻¹' open) (using source ⊆ σ.target to absorb σ.target)
  -- Hence A_id is open as intersection of two opens.
  convert h_src_open.inter h_target_inter_open using 1
  ext y
  refine ⟨fun hy => ⟨hy.1, h_subset hy.1, hy.2⟩, fun hy => ⟨hy.1, hy.2.2⟩⟩

/-- **`chartTransitionNegPieceOpen`** — the neg-piece `A_neg` is open. -/
lemma chartTransitionNegPieceOpen (s s' : S4) :
    IsOpen (((S4.chartRP4 s).symm.trans (S4.chartRP4 s')).source ∩
      {y | (⟨-(((stereographic' 4 (-s)).symm y : S4) : EuclideanSpace ℝ (Fin 5)),
              neg_mem_S4_of_mem_S4 ((stereographic' 4 (-s)).symm y).property⟩ : S4) ∈
        ((Subtype.val ⁻¹' Metric.ball (s' : EuclideanSpace ℝ (Fin 5)) 1) : Set S4)}) := by
  set σ := stereographic' 4 (-s)
  set source := ((S4.chartRP4 s).symm.trans (S4.chartRP4 s')).source
  -- A_neg = source ∩ {y | -(σ.symm y).val ∈ ball(s', 1)} = source ∩ {y | (σ.symm y).val ∈ ball(-s', 1)}
  have h_src_open : IsOpen source :=
    ((S4.chartRP4 s).symm.trans (S4.chartRP4 s')).open_source
  have h_subset : source ⊆ σ.target :=
    chartTransitionSource_subset_stereographic_target s s'
  -- ball(-s', 1) on S4 is open
  have h_ball_open : IsOpen ((Subtype.val ⁻¹'
      Metric.ball (-(s' : EuclideanSpace ℝ (Fin 5))) 1) : Set S4) :=
    Metric.isOpen_ball.preimage continuous_subtype_val
  have h_target_inter_open : IsOpen (σ.target ∩ σ.symm ⁻¹' _) :=
    σ.isOpen_inter_preimage_symm h_ball_open
  -- The key equivalence: -x.val ∈ ball(s'.val, 1) ↔ x.val ∈ ball(-s'.val, 1)
  -- via `dist (-a) b = ‖-(a + b)‖ = ‖a + b‖ = ‖a - (-b)‖ = dist a (-b)`.
  have h_equiv : ∀ x : EuclideanSpace ℝ (Fin 5),
      -x ∈ Metric.ball (s' : EuclideanSpace ℝ (Fin 5)) 1 ↔
      x ∈ Metric.ball (-(s' : EuclideanSpace ℝ (Fin 5))) 1 := by
    intro x
    simp only [Metric.mem_ball, dist_eq_norm]
    constructor
    · intro h
      have : ‖x - (-(s' : EuclideanSpace ℝ (Fin 5)))‖ = ‖-x - (s' : EuclideanSpace ℝ (Fin 5))‖ := by
        rw [show x - -(s' : EuclideanSpace ℝ (Fin 5)) =
            -(-x - (s' : EuclideanSpace ℝ (Fin 5))) by abel, norm_neg]
      rw [this]; exact h
    · intro h
      have : ‖-x - (s' : EuclideanSpace ℝ (Fin 5))‖ = ‖x - (-(s' : EuclideanSpace ℝ (Fin 5)))‖ := by
        rw [show -x - (s' : EuclideanSpace ℝ (Fin 5)) =
            -(x - -(s' : EuclideanSpace ℝ (Fin 5))) by abel, norm_neg]
      rw [this]; exact h
  convert h_src_open.inter h_target_inter_open using 1
  ext y
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage]
  refine ⟨fun hy => ⟨hy.1, h_subset hy.1, ?_⟩, fun hy => ⟨hy.1, ?_⟩⟩
  · -- hy.2 : (⟨-x.val, ...⟩ : S4) ∈ Subtype.val ⁻¹' ball s'.val 1 = (-x.val ∈ ball s'.val 1)
    -- Goal: (σ.symm y).val ∈ ball (-s'.val) 1
    exact (h_equiv _).mp hy.2
  · -- Goal: (⟨-x.val, ...⟩ : S4) ∈ Subtype.val ⁻¹' ball s'.val 1, i.e., -x.val ∈ ball s'.val 1
    -- hy.2 : (σ.symm y).val ∈ ball (-s'.val) 1
    exact (h_equiv _).mpr hy.2.2

/-! ## §8. Source inclusions for ContDiffOn.mono on each piece -/

/-- **`chartTransitionIdPiece_subset_sphere_transition_source`** — the id-piece
is a subset of the sphere chart-transition source `(stereographic' 4 (-s)).symm.trans
(stereographic' 4 (-s'))`. -/
lemma chartTransitionIdPiece_subset_sphere_transition_source (s s' : S4) :
    (((S4.chartRP4 s).symm.trans (S4.chartRP4 s')).source ∩
      {y | ((stereographic' 4 (-s)).symm y : S4) ∈
        ((Subtype.val ⁻¹' Metric.ball (s' : EuclideanSpace ℝ (Fin 5)) 1) : Set S4)}) ⊆
      ((stereographic' 4 (-s)).symm.trans (stereographic' 4 (-s'))).source := by
  intro y hy
  -- y ∈ source ⊆ σ.target (substrate lemma) and σ.symm y ∈ ball(s', 1) ∩ S4 (from hy.2)
  -- Need: y ∈ (σ.symm.trans σ').source = σ.target ∩ σ.symm ⁻¹' σ'.source
  -- σ'.source = S4 ∖ {-(-s')} = S4 ∖ {s'}.
  -- For σ.symm y ∈ ball(s', 1) ∩ S4 and s' ∉ ball(-s', 1) implies σ.symm y ≠ -s'? No, we need ≠ s'.
  -- σ.symm y ∈ ball(s', 1): so distance < 1, but s' ∈ ball(s', 1) too. So σ.symm y could equal s'.
  -- Wait — if σ.symm y = s' and s' ∈ ball(s', 1), that's consistent. So σ.symm y MIGHT equal s'.
  -- In that case y is in the sphere transition source iff σ.symm y ≠ -(-s') = s' too — contradiction.
  -- Hmm. So this inclusion might not hold pointwise.
  -- BUT: if σ.symm y = s', then the chart-transition value at y matches σ' (s') = stereographic' 4 (-s')(s')
  -- but s' ∉ source of stereographic' 4 (-s')! So actually y is NOT in source either.
  -- Hmm, let me reconsider. For y ∈ source of (chartRP4 s).symm.trans (chartRP4 s'):
  -- We need (chartRP4 s).symm y ∈ (chartRP4 s').source = (toRP4_localOH s').target.
  -- (chartRP4 s).symm y = toRP4 (σ.symm y). For toRP4 (σ.symm y) ∈ toRP4 '' (ball(s', 1) ∩ S4),
  -- need σ.symm y ∈ ball(s', 1) OR -σ.symm y ∈ ball(s', 1). Either way σ.symm y ≠ s'?
  -- If σ.symm y = s': then σ.symm y ∈ ball(s', 1) (since s' ∈ ball(s', 1) trivially).
  -- So id-piece. But also σ.symm y = s' means we're at the excluded point of σ'.source.
  -- BUT (chartRP4 s').source = (toRP4_localOH s').target — this requires the source-condition of σ' too?
  -- Let me unfold (chartRP4 s').source.
  -- (chartRP4 s') = (toRP4_localOH s').symm.trans (stereographic' 4 (-s'))
  -- (chartRP4 s').source = (toRP4_localOH s').symm.source ∩ (toRP4_localOH s').symm ⁻¹' σ'.source
  --                     = (toRP4_localOH s').target ∩ (toRP4_localOH s').symm ⁻¹' (S4 ∖ {-(-s')})
  --                     = (toRP4_localOH s').target ∩ (toRP4_localOH s').symm ⁻¹' (S4 ∖ {s'})
  -- For toRP4 x ∈ (chartRP4 s').source, (toRP4_localOH s').symm (toRP4 x) must be in S4 ∖ {s'}.
  -- If σ.symm y = s', then x = s' (in id-piece), (toRP4_localOH s').symm (toRP4 s') = s' ∈ {s'}, excluded.
  -- So y is NOT in source if σ.symm y = s' (in id-piece).
  -- Hmm interesting. So actually on the id-piece, σ.symm y ≠ s'. Hence A_id ⊆ sphere transition source.
  refine ⟨?_, ?_⟩
  · -- y ∈ σ.target via source ⊆ σ.target
    exact chartTransitionSource_subset_stereographic_target s s' hy.1
  · -- σ.symm y ∈ σ'.source = S4 ∖ {-(-s')} = S4 ∖ {s'}
    show (stereographic' 4 (-s)).symm y ∈ (stereographic' 4 (-s')).source
    -- σ.symm y ∈ ball(s', 1) ∩ S4 (from hy.2)
    -- σ'.source: x ∈ S4 with x.val ≠ ((-(-s')) : S4).val = s'.val
    -- i.e., σ.symm y ≠ s' as subtype.
    -- By the analysis above: if σ.symm y = s', then (chartRP4 s).symm y = toRP4 s', and we need this ∈ (chartRP4 s').source = (toRP4_localOH s').target ∩ section ⁻¹' (σ'.source). The section at toRP4 s' returns s' (the canonical preimage in ball(s', 1)). But s' ∉ σ'.source. So y ∉ source. Contradiction.
    have h_y_in_src : y ∈ ((S4.chartRP4 s).symm.trans (S4.chartRP4 s')).source := hy.1
    have h_chart_s'_src :
        (S4.chartRP4 s).symm y ∈ (S4.chartRP4 s').source := h_y_in_src.2
    set x : S4 := (stereographic' 4 (-s)).symm y
    have h_chart_symm_eq : (S4.chartRP4 s).symm y = S4.toRP4 x := rfl
    rw [h_chart_symm_eq] at h_chart_s'_src
    -- h_chart_s'_src : S4.toRP4 x ∈ (S4.chartRP4 s').source
    -- (S4.chartRP4 s').source = (toRP4_localOH s').symm.trans σ' .source
    -- = (toRP4_localOH s').target ∩ (toRP4_localOH s').symm ⁻¹' σ'.source
    have h_chart_src_unfold :
        S4.toRP4 x ∈ (S4.toRP4_localOpenPartialHomeomorph s').target ∧
        (S4.toRP4_localOpenPartialHomeomorph s').symm (S4.toRP4 x) ∈
          (stereographic' 4 (-s')).source := by
      exact h_chart_s'_src
    -- On id-piece: x ∈ ball(s', 1), so (toRP4_localOH s').symm (toRP4 x) = x by helper §2.
    have h_section : (S4.toRP4_localOpenPartialHomeomorph s').symm (S4.toRP4 x) = x :=
      S4.toRP4_localOH_symm_eq_self_of_mem_ball s' x hy.2
    rw [h_section] at h_chart_src_unfold
    -- Now h_chart_src_unfold.2 : x ∈ σ'.source, which is what we want.
    exact h_chart_src_unfold.2

/-! ## §9. ContDiffOn on the id-piece via sphere chart-transition + congr -/

/-- **`chartTransition_contDiffOn_idPiece`** — `ContDiffOn ℝ ω` of the chart-
transition forward map restricted to the id-piece. Discharge via
`sphere_chart_transition_contDiffOn (-s) (-s')` + `ContDiffOn.mono` +
`ContDiffOn.congr` (using `chartTransition_forward_eq_sphere_on_id_piece`). -/
lemma chartTransition_contDiffOn_idPiece (s s' : S4) :
    ContDiffOn ℝ ω (↑((S4.chartRP4 s).symm.trans (S4.chartRP4 s')))
      (((S4.chartRP4 s).symm.trans (S4.chartRP4 s')).source ∩
        {y | ((stereographic' 4 (-s)).symm y : S4) ∈
          ((Subtype.val ⁻¹' Metric.ball (s' : EuclideanSpace ℝ (Fin 5)) 1) : Set S4)}) := by
  -- Strategy: sphere transition smoothness + mono + congr.
  have h_sphere_cd : ContDiffOn ℝ ω
      (↑((stereographic' 4 (-s)).symm.trans (stereographic' 4 (-s'))))
      ((stereographic' 4 (-s)).symm.trans (stereographic' 4 (-s'))).source :=
    sphere_chart_transition_contDiffOn (-s) (-s')
  have h_mono := h_sphere_cd.mono
    (chartTransitionIdPiece_subset_sphere_transition_source s s')
  -- Now use congr: forward map equals sphere transition on A_id.
  apply h_mono.congr
  intro y hy
  -- Forward map equality on A_id via chartTransition_forward_eq_sphere_on_id_piece.
  exact chartTransition_forward_eq_sphere_on_id_piece s s' y hy.2

/-! ## §10. ContDiffOn on the neg-piece via ContMDiff antipode + chart conjugation -/

/-- **`chartTransition_contDiffOn_negPiece`** — `ContDiffOn ℝ ω` of the chart-
transition forward map restricted to the neg-piece. Discharge via
`contMDiff_neg_sphere` (Mathlib) + `contMDiffOn_iff_of_mem_maximalAtlas'`
(extract chart-conjugate as ContDiffOn) + `ContDiffOn.mono` + `ContDiffOn.congr`
(using `chartTransition_forward_eq_neg_sphere_on_neg_piece`). -/
lemma chartTransition_contDiffOn_negPiece (s s' : S4) :
    ContDiffOn ℝ ω (↑((S4.chartRP4 s).symm.trans (S4.chartRP4 s')))
      (((S4.chartRP4 s).symm.trans (S4.chartRP4 s')).source ∩
        {y | (⟨-(((stereographic' 4 (-s)).symm y : S4) : EuclideanSpace ℝ (Fin 5)),
              neg_mem_S4_of_mem_S4 ((stereographic' 4 (-s)).symm y).property⟩ : S4) ∈
          ((Subtype.val ⁻¹' Metric.ball (s' : EuclideanSpace ℝ (Fin 5)) 1) : Set S4)}) := by
  set σ := stereographic' 4 (-s)
  set σ' := stereographic' 4 (-s')
  let antipode : S4 → S4 := fun x =>
    ⟨-(x : EuclideanSpace ℝ (Fin 5)), neg_mem_S4_of_mem_S4 x.property⟩
  set A_neg := ((S4.chartRP4 s).symm.trans (S4.chartRP4 s')).source ∩
    {y | (⟨-(((stereographic' 4 (-s)).symm y : S4) : EuclideanSpace ℝ (Fin 5)),
            neg_mem_S4_of_mem_S4 ((stereographic' 4 (-s)).symm y).property⟩ : S4) ∈
      ((Subtype.val ⁻¹' Metric.ball (s' : EuclideanSpace ℝ (Fin 5)) 1) : Set S4)}
  -- antipode is ContMDiff via Mathlib's contMDiff_neg_sphere
  have h_antipode_cmd : ContMDiff (𝓡 4) (𝓡 4) ω antipode := contMDiff_neg_sphere
  -- σ.symm '' A_neg ⊆ σ.source (since A_neg ⊆ σ.target)
  have h_A_neg_subset_target : A_neg ⊆ σ.target := fun y hy =>
    chartTransitionSource_subset_stereographic_target s s' hy.1
  -- Let preImg := σ.symm '' A_neg
  set preImg : Set S4 := σ.symm '' A_neg
  have h_preImg_subset_src : preImg ⊆ σ.source := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact σ.map_target (h_A_neg_subset_target hy)
  -- MapsTo antipode preImg σ'.source
  -- σ'.source = (stereographic' 4 (-s')).source = {-s'}ᶜ (per Mathlib stereographic'_source convention).
  -- For x = σ.symm y with y ∈ A_neg, antipode x = -x. Need -x ≠ -s', i.e., x ≠ s'.
  -- For y ∈ A_neg, -σ.symm y ∈ ball(s', 1). If σ.symm y = s' then -s' ∈ ball(s', 1), contradiction
  -- (distance(-s', s') = 2 > 1).
  have h_mapsTo : Set.MapsTo antipode preImg σ'.source := by
    intro x hx
    obtain ⟨y, hy_A, rfl⟩ := hx
    show antipode (σ.symm y) ∈ σ'.source
    rw [stereographic'_source]
    -- Goal: antipode (σ.symm y) ∈ ({-s'} : Set S4)ᶜ, i.e., antipode (σ.symm y) ≠ -s'
    intro h_eq
    rw [Set.mem_singleton_iff] at h_eq
    -- h_eq : antipode (σ.symm y) = -s', i.e., -σ.symm y = -s' (as subtype), i.e., σ.symm y = s'
    have h_val_eq : ((σ.symm y : S4) : EuclideanSpace ℝ (Fin 5)) =
        (s' : EuclideanSpace ℝ (Fin 5)) := by
      have h1 : (antipode (σ.symm y) : EuclideanSpace ℝ (Fin 5)) =
          -((σ.symm y : S4) : EuclideanSpace ℝ (Fin 5)) := rfl
      have h2 : ((-s' : S4) : EuclideanSpace ℝ (Fin 5)) =
          -((s' : S4) : EuclideanSpace ℝ (Fin 5)) := rfl
      have h3 : -((σ.symm y : S4) : EuclideanSpace ℝ (Fin 5)) =
          -((s' : S4) : EuclideanSpace ℝ (Fin 5)) := by
        rw [← h1, ← h2]; exact congr_arg Subtype.val h_eq
      have h4 := congr_arg Neg.neg h3
      simp only [neg_neg] at h4
      exact h4
    -- Now σ.symm y = s' (as Subtype). From hy_A.2: ⟨-σ.symm y.val, ...⟩ ∈ ball(s', 1) ∩ S4.
    -- So -σ.symm y.val ∈ ball(s'.val, 1). With h_val_eq, σ.symm y.val = s'.val, so -s'.val ∈ ball(s'.val, 1).
    -- But dist(-s'.val, s'.val) = ‖-s'.val - s'.val‖ = ‖-2 • s'.val‖ = 2 (since ‖s'.val‖=1), contradiction.
    have h_neg_in_ball : -((σ.symm y : S4) : EuclideanSpace ℝ (Fin 5)) ∈
        Metric.ball (s' : EuclideanSpace ℝ (Fin 5)) 1 := hy_A.2
    rw [h_val_eq] at h_neg_in_ball
    -- h_neg_in_ball : -s'.val ∈ ball(s'.val, 1), i.e., dist(-s'.val, s'.val) < 1
    simp only [Metric.mem_ball] at h_neg_in_ball
    have h_s'_norm : ‖((s' : S4) : EuclideanSpace ℝ (Fin 5))‖ = 1 := by
      have : ((s' : S4) : EuclideanSpace ℝ (Fin 5)) ∈
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 := s'.property
      rwa [Metric.mem_sphere, dist_zero_right] at this
    have h_dist : dist (-((s' : S4) : EuclideanSpace ℝ (Fin 5)))
        ((s' : S4) : EuclideanSpace ℝ (Fin 5)) = 2 := by
      rw [dist_eq_norm]
      have h_diff : -((s' : S4) : EuclideanSpace ℝ (Fin 5)) -
          ((s' : S4) : EuclideanSpace ℝ (Fin 5)) =
          (-2 : ℝ) • ((s' : S4) : EuclideanSpace ℝ (Fin 5)) := by
        rw [neg_smul, two_smul]; abel
      rw [h_diff, norm_smul, h_s'_norm, mul_one, Real.norm_eq_abs, abs_neg, abs_of_pos]
      norm_num
    linarith [h_neg_in_ball]
  -- Now apply contMDiffOn_iff_of_mem_maximalAtlas' to extract ContDiffOn of chart-conjugate
  have he : σ ∈ IsManifold.maximalAtlas (𝓡 4) ω S4 :=
    StructureGroupoid.subset_maximalAtlas _ ⟨-s, rfl⟩
  have he' : σ' ∈ IsManifold.maximalAtlas (𝓡 4) ω S4 :=
    StructureGroupoid.subset_maximalAtlas _ ⟨-s', rfl⟩
  have h_antipode_cmd_on : ContMDiffOn (𝓡 4) (𝓡 4) ω antipode preImg :=
    h_antipode_cmd.contMDiffOn
  have h_chart_conjugate_cd : ContDiffOn ℝ ω
      ((σ'.extend (𝓡 4)) ∘ antipode ∘ (σ.extend (𝓡 4)).symm) ((σ.extend (𝓡 4)) '' preImg) :=
    ((contMDiffOn_iff_of_mem_maximalAtlas' he he' h_preImg_subset_src h_mapsTo).mp
      h_antipode_cmd_on)
  -- Simplify extend for modelWithCornersSelf
  simp only [OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl] at h_chart_conjugate_cd
  -- Now h_chart_conjugate_cd : ContDiffOn ω (σ' ∘ antipode ∘ σ.symm) (σ '' preImg)
  -- And σ '' preImg = σ '' (σ.symm '' A_neg) = A_neg (since A_neg ⊆ σ.target).
  have h_image_eq : σ '' preImg = A_neg := by
    rw [show preImg = σ.symm '' A_neg from rfl]
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x, ⟨y', hy', rfl⟩, hxy⟩
      have h_eq : σ (σ.symm y') = y' := σ.right_inv (h_A_neg_subset_target hy')
      rw [h_eq] at hxy
      rw [← hxy]
      exact hy'
    · intro hy
      refine ⟨σ.symm y, ⟨y, hy, rfl⟩, ?_⟩
      exact σ.right_inv (h_A_neg_subset_target hy)
  have h_chart_conjugate_cd' : ContDiffOn ℝ ω
      (↑σ'.toPartialEquiv ∘ antipode ∘ ↑σ.symm) A_neg := by
    rw [← h_image_eq]
    convert h_chart_conjugate_cd using 1
  -- Use ContDiffOn.congr with chartTransition_forward_eq_neg_sphere_on_neg_piece.
  apply h_chart_conjugate_cd'.congr
  intro y hy
  show ((S4.chartRP4 s).symm.trans (S4.chartRP4 s')) y =
       (↑σ'.toPartialEquiv ∘ antipode ∘ ↑σ.symm) y
  rw [chartTransition_forward_eq_neg_sphere_on_neg_piece s s' y hy.2]
  rfl

/-! ## §11. M3 Layer B-4d FINAL CLOSURE: full `IsManifold (𝓡 4) ω RP4` -/

/-- **`RP4.chart_transition_smoothness_pair`** — the chart transition between
two atlas charts of RP⁴ is `ContDiffOn ℝ ω` on its source. Discharge via
`chartTransition_contDiffOn_idPiece` + `chartTransition_contDiffOn_negPiece`
+ `chartTransitionSource_eq_id_union_neg` + `ContDiffOn.union_of_isOpen`. -/
theorem RP4.chart_transition_smoothness_pair (s s' : S4) :
    ContDiffOn ℝ ω (↑((S4.chartRP4 s).symm.trans (S4.chartRP4 s')))
      ((S4.chartRP4 s).symm.trans (S4.chartRP4 s')).source := by
  rw [chartTransitionSource_eq_id_union_neg s s']
  exact ContDiffOn.union_of_isOpen
    (chartTransition_contDiffOn_idPiece s s')
    (chartTransition_contDiffOn_negPiece s s')
    (chartTransitionIdPieceOpen s s')
    (chartTransitionNegPieceOpen s s')

/-- **`RP4.instIsManifold`** — `RP⁴` is an analytic 4-manifold.

**M3 Layer B-4d FINAL CLOSURE.** The chart transitions of the RP⁴
atlas are `ContDiffOn ℝ ω` via the piecewise decomposition:

- **A_id-piece** (where the toRP4 section through s' picks the same
  preimage as through s): transition equals the sphere chart-transition
  between `stereographic' 4 (-s)` and `stereographic' 4 (-s')`,
  ContDiffOn via `sphere_chart_transition_contDiffOn`.
- **A_neg-piece** (where the section picks the antipodal preimage):
  transition equals the chart-conjugate of the antipodal map on S⁴,
  ContDiffOn via `contMDiff_neg_sphere` +
  `contMDiffOn_iff_of_mem_maximalAtlas'`.

The two open pieces are disjoint (B-1 antipodal-disjoint balls) and
cover the source. Union via `ContDiffOn.union_of_isOpen`.

This closes Phase 6r-prime M3 Layer B-4d at the **instance level**. -/
noncomputable instance RP4.instIsManifold : IsManifold (𝓡 4) ω RP4 := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨s, rfl⟩ ⟨s', rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
    Set.preimage_id, Set.inter_univ, Function.id_comp, Function.comp_id]
  exact RP4.chart_transition_smoothness_pair s s'

end SKEFTHawking.SymTFT
