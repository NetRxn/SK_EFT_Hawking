/-
# Regular value theorem — the level set of a real submersion is a smooth codim-1 submanifold

This module upgrades the *local* transversality bricks of `SmithTransversality.lean` to a genuine
**smooth-manifold structure** on the level set of a real submersion, built on Mathlib's implicit
function theorem (`HasStrictFDerivAt.implicitToOpenPartialHomeomorph`).

## What is built (all kernel-pure: only {propext, Classical.choice, Quot.sound})

**1. The chart-local core (general, fully nonlinear).** For a strictly-differentiable `f : E → ℝ`
with surjective derivative `f'` at a regular point `a` (`f a = 0`), `levelSetChart` is a genuine
`OpenPartialHomeomorph` from the subtype `↥(zeroLocus f)` to the codimension-1 model `ker f'`,
obtained from the IFT chart `Φ : E ≈ ℝ × ker f'` by restricting to the slice `{first coord = 0}`
(which is exactly the level set in the chart). This is *the* load-bearing local model of the regular
value theorem: near a regular point the level set is a smooth codim-1 chart domain. Companion
characterization lemmas: `levelSetChart_apply/_source/_target`, `mem_levelSetChart_source`,
`levelSetChart_apply_base`.

**2. Full manifold structure + smooth embedding (affine submersion, fixed model).** For an *affine*
submersion (constant derivative `f'`, e.g. `f x = f' x - c`), the level set `affineLevelSet f' c`
carries genuine `ChartedSpace` and `IsManifold` *instances* over a fixed codim-1 model `K` (any normed
space with a continuous linear equivalence `K ≃L ker f'`), with a single global chart, and the
inclusion `Subtype.val : ↥(affineLevelSet f' c) → E` is both a topological embedding
(`affine_isEmbedding_subtypeVal`) and `C^∞` (`affine_contMDiff_subtypeVal`) — i.e. a smooth embedding.
The Euclidean instantiation `K = EuclideanSpace ℝ (Fin (finrank ℝ (ker f')))` gives the textbook
"smooth manifold modelled on `ℝⁿ⁻¹`" (`euclideanAffine*`). `affineLevelSet_eq_zeroLocus` ties the
affine sets to the general `zeroLocus`.

## Scope boundary (honest)

The full `ChartedSpace`/`IsManifold` for a *general nonlinear* `f` (where the kernel `ker(f' p)` varies
with the base point) is NOT assembled here: it additionally requires (a) a fixed model with per-point
continuous-linear identifications `K ≃L ker(f' p)`, (b) `C^∞`-ness of `implicitToOpenPartialHomeomorph`
itself (Mathlib provides `ContDiffAt.implicitFunction` only for the `ImplicitFunctionData` form, which
would need substantial bridging), and (c) the resulting transition-map smoothness between charts at
different points. Item 1 above is the local model on which that global assembly would be built.

Kernel-pure; no axioms beyond Mathlib's core {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import SKEFTHawking.SmithTransversality

namespace SKEFTHawking.SmithRegularValue

open scoped Topology Classical
open Manifold

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The zero locus `f ⁻¹' {0}` of a function `f : E → ℝ`, as a set. -/
def zeroLocus (f : E → ℝ) : Set E := f ⁻¹' {0}

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
@[simp] theorem mem_zeroLocus {f : E → ℝ} {x : E} : x ∈ zeroLocus f ↔ f x = 0 := Iff.rfl

/-- Abbreviation for the codimension-1 model space `ker f'` of the level set at a regular point. -/
abbrev kerModel (f' : E →L[ℝ] ℝ) : Type _ := LinearMap.ker (f' : E →ₗ[ℝ] ℝ)

variable (f : E → ℝ) (f' : E →L[ℝ] ℝ) (a : E)
  (hf : HasStrictFDerivAt f f' a) (hf' : (f' : E →L[ℝ] ℝ).range = ⊤) (h0 : f a = 0)

/-- The IFT chart `Φ : E ≈ ℝ × ker f'` at a regular point `a`, with `(Φ x).1 = f x`. -/
def iftChart : OpenPartialHomeomorph E (ℝ × kerModel f') :=
  hf.implicitToOpenPartialHomeomorph f f' hf'

theorem iftChart_fst (x : E) : (iftChart f f' a hf hf' x).1 = f x :=
  hf.implicitToOpenPartialHomeomorph_fst hf' x

theorem mem_iftChart_source : a ∈ (iftChart f f' a hf hf').source :=
  hf.mem_implicitToOpenPartialHomeomorph_source hf'

theorem iftChart_symm_fst_eq_zero {k : kerModel f'}
    (hk : (0, k) ∈ (iftChart f f' a hf hf').target) :
    f ((iftChart f f' a hf hf').symm (0, k)) = 0 := by
  have hmem : (iftChart f f' a hf hf').symm (0, k) ∈ (iftChart f f' a hf hf').source :=
    (iftChart f f' a hf hf').map_target hk
  have := iftChart_fst f f' a hf hf' ((iftChart f f' a hf hf').symm (0, k))
  rw [(iftChart f f' a hf hf').right_inv hk] at this
  simpa using this.symm

/-- **The level-set chart at a regular point.** For a strictly-differentiable real submersion `f`
with surjective derivative `f'` at `a`, this is the chart of the smooth submanifold structure on the
level set `zeroLocus f = f⁻¹(0)`: an `OpenPartialHomeomorph` from the subtype `↥(zeroLocus f)` to the
codimension-1 model `ker f'`, obtained from the IFT chart `Φ : E ≈ ℝ × ker f'` by restricting to the
slice `{first coordinate = 0}` (which is exactly the level set in the chart). -/
def levelSetChart : OpenPartialHomeomorph (zeroLocus f) (kerModel f') where
  toFun := fun x => (iftChart f f' a hf hf' x.1).2
  invFun := fun k =>
    if hk : (0, k) ∈ (iftChart f f' a hf hf').target then
      ⟨(iftChart f f' a hf hf').symm (0, k), iftChart_symm_fst_eq_zero f f' a hf hf' hk⟩
    else ⟨a, by simpa using h0⟩
  source := Subtype.val ⁻¹' (iftChart f f' a hf hf').source
  target := (Prod.mk (0 : ℝ)) ⁻¹' (iftChart f f' a hf hf').target
  map_source' := by
    intro x hx
    have hxs : x.1 ∈ (iftChart f f' a hf hf').source := hx
    have hmap := (iftChart f f' a hf hf').map_source hxs
    have hfst : (iftChart f f' a hf hf' x.1).1 = 0 := by rw [iftChart_fst]; exact x.2
    have heq : (0, (iftChart f f' a hf hf' x.1).2) = iftChart f f' a hf hf' x.1 := by
      rw [← hfst]
    rw [Set.mem_preimage, heq]; exact hmap
  map_target' := by
    intro x hx
    have hxt : (0, x) ∈ (iftChart f f' a hf hf').target := hx
    rw [Set.mem_preimage]
    simp only [dif_pos hxt]
    exact (iftChart f f' a hf hf').map_target hxt
  left_inv' := by
    intro x hx
    have hxs : x.1 ∈ (iftChart f f' a hf hf').source := hx
    have hmap := (iftChart f f' a hf hf').map_source hxs
    have hfst : (iftChart f f' a hf hf' x.1).1 = 0 := by rw [iftChart_fst]; exact x.2
    have heq : (0, (iftChart f f' a hf hf' x.1).2) = iftChart f f' a hf hf' x.1 := by
      rw [← hfst]
    have hmem : (0, (iftChart f f' a hf hf' x.1).2) ∈ (iftChart f f' a hf hf').target := by
      rw [heq]; exact hmap
    simp only [dif_pos hmem]
    apply Subtype.ext
    show (iftChart f f' a hf hf').symm (0, (iftChart f f' a hf hf' x.1).2) = x.1
    rw [heq, (iftChart f f' a hf hf').left_inv hxs]
  right_inv' := by
    intro k hk
    have hkt : (0, k) ∈ (iftChart f f' a hf hf').target := hk
    simp only [dif_pos hkt]
    show (iftChart f f' a hf hf' ((iftChart f f' a hf hf').symm (0, k))).2 = k
    rw [(iftChart f f' a hf hf').right_inv hkt]
  open_source :=
    (iftChart f f' a hf hf').open_source.preimage continuous_subtype_val
  open_target :=
    (iftChart f f' a hf hf').open_target.preimage (continuous_const.prodMk continuous_id)
  continuousOn_toFun := by
    apply ContinuousOn.snd
    exact ((iftChart f f' a hf hf').continuousOn_toFun.comp continuous_subtype_val.continuousOn
      (fun x hx => hx))
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    apply ContinuousOn.congr (f := fun k => (iftChart f f' a hf hf').symm (0, k))
    · exact ((iftChart f f' a hf hf').continuousOn_invFun.comp
        (continuous_const.prodMk continuous_id).continuousOn (fun k hk => hk))
    · intro k hk
      have hkt : (0, k) ∈ (iftChart f f' a hf hf').target := hk
      simp only [Function.comp_apply, dif_pos hkt]

@[simp] theorem levelSetChart_apply (x : zeroLocus f) :
    levelSetChart f f' a hf hf' h0 x = (iftChart f f' a hf hf' x.1).2 := rfl

@[simp] theorem levelSetChart_source :
    (levelSetChart f f' a hf hf' h0).source = Subtype.val ⁻¹' (iftChart f f' a hf hf').source := rfl

@[simp] theorem levelSetChart_target :
    (levelSetChart f f' a hf hf' h0).target =
      (Prod.mk (0 : ℝ)) ⁻¹' (iftChart f f' a hf hf').target := rfl

/-- The basepoint `a` (as a point of the level set) lies in the source of its chart. -/
theorem mem_levelSetChart_source :
    (⟨a, by simpa using h0⟩ : zeroLocus f) ∈ (levelSetChart f f' a hf hf' h0).source := by
  rw [levelSetChart_source, Set.mem_preimage]
  exact mem_iftChart_source f f' a hf hf'

/-- The chart at the basepoint sends `a` to `0 ∈ ker f'`. -/
theorem levelSetChart_apply_base :
    levelSetChart f f' a hf hf' h0 ⟨a, by simpa using h0⟩ = 0 := by
  rw [levelSetChart_apply]
  have : iftChart f f' a hf hf' a = (f a, 0) :=
    hf.implicitToOpenPartialHomeomorph_self hf'
  rw [this]

end

/-!
## Global manifold structure: the affine submersion case

For an **affine** submersion `f x = f' x - c` (equivalently: `f` has the *same* derivative `f'` at every
point), the level set `affineLevelSet f' c = {x | f' x = c}` is a coset of `ker f'` and carries a genuine
smooth-manifold structure modelled on a fixed codimension-1 space `K` (any normed space with a
continuous linear equivalence `e : K ≃L ker f'`), witnessed by a single global chart. This produces
honest `ChartedSpace` and `IsManifold` instances over a fixed model, with a smooth embedding into `E`.
Taking `K = ker f'`, `e = .refl` recovers the literal `ker f'` model; the finite-dimensional Euclidean
instantiation is in the `EuclideanModel` section below.
-/

section Affine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
  (f' : E →L[ℝ] ℝ) (c : ℝ) (e : K ≃L[ℝ] LinearMap.ker (f' : E →ₗ[ℝ] ℝ))

/-- The affine level set `{x | f' x = c}`, as a set. -/
def affineLevelSet : Set E := {x | f' x = c}

@[simp] theorem mem_affineLevelSet {x : E} : x ∈ affineLevelSet f' c ↔ f' x = c := Iff.rfl

/-- The affine level set `{f' = c}` is exactly the zero locus of the affine submersion `x ↦ f' x - c`,
tying the global affine manifold structure to the general per-point `levelSetChart` construction. -/
theorem affineLevelSet_eq_zeroLocus :
    affineLevelSet f' c = zeroLocus (fun x => f' x - c) := by
  ext x
  simp only [mem_affineLevelSet, mem_zeroLocus, sub_eq_zero]

/-- A distinguished basepoint of a nonempty affine level set, chosen by `Classical.choice`. -/
noncomputable def affineBasePoint [hne : Nonempty (affineLevelSet f' c)] : E :=
  (Classical.choice hne).1

theorem affineBasePoint_mem [hne : Nonempty (affineLevelSet f' c)] :
    f' (affineBasePoint f' c) = c := (Classical.choice hne).2

/-- The single global chart of the affine level set, valued in a fixed codim-1 model `K` carrying a
continuous linear equivalence `e : K ≃L ker f'`: `x ↦ e.symm (x - x₀)`, with inverse `k ↦ x₀ + e k`,
where `x₀` is the distinguished basepoint. A composition of a translation and the linear iso `e`,
hence a homeomorphism `{f' = c} ≃ K`. (`K = ker f'` with `e = .refl` recovers the literal model;
`K = EuclideanSpace ℝ (Fin (n-1))` gives a Euclidean chart.) -/
noncomputable def affineChart [Nonempty (affineLevelSet f' c)] :
    OpenPartialHomeomorph (affineLevelSet f' c) K where
  toFun := fun x => e.symm ⟨x.1 - affineBasePoint f' c, by
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub]
    have hx : f' x.1 = c := x.2
    rw [hx, affineBasePoint_mem, sub_self]⟩
  invFun := fun k => ⟨affineBasePoint f' c + (e k : E), by
    have hk : f' (e k : E) = 0 := (e k).2
    simp only [mem_affineLevelSet, map_add, hk, add_zero, affineBasePoint_mem]⟩
  source := Set.univ
  target := Set.univ
  map_source' := fun _ _ => Set.mem_univ _
  map_target' := fun _ _ => Set.mem_univ _
  left_inv' := fun x _ => by
    apply Subtype.ext
    simp only [ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]
  right_inv' := fun k _ => by
    simp only [add_sub_cancel_left]
    rw [Subtype.coe_eta, ContinuousLinearEquiv.symm_apply_apply]
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := by
    apply Continuous.continuousOn
    exact e.symm.continuous.comp ((continuous_subtype_val.sub continuous_const).subtype_mk _)
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    exact (continuous_const.add ((continuous_subtype_val).comp e.continuous)).continuousOn

@[simp] theorem affineChart_source [Nonempty (affineLevelSet f' c)] :
    (affineChart f' c e).source = Set.univ := rfl

@[simp] theorem affineChart_target [Nonempty (affineLevelSet f' c)] :
    (affineChart f' c e).target = Set.univ := rfl

theorem affineChart_symm_apply [Nonempty (affineLevelSet f' c)] (k : K) :
    ((affineChart f' c e).symm k : E) = affineBasePoint f' c + (e k : E) := rfl

/-- **The affine level set is a charted space over the fixed codim-1 model `K`**, with the single
global chart. A genuine `ChartedSpace` instance over the fixed model. -/
noncomputable instance affineChartedSpace [Nonempty (affineLevelSet f' c)] :
    ChartedSpace K (affineLevelSet f' c) where
  atlas := {affineChart f' c e}
  chartAt := fun _ => affineChart f' c e
  mem_chart_source := fun x => by rw [affineChart_source]; exact Set.mem_univ _
  chart_mem_atlas := fun _ => rfl

/-- **The affine level set is a `C^∞` manifold over the fixed model `K`.** The single-chart atlas makes
the structure-groupoid compatibility immediate (the only transition is `e.symm ≫ₕ e`). This is the
affine regular-value theorem with a genuine `IsManifold` instance over a fixed codim-1 model. -/
instance affineHasGroupoid [Nonempty (affineLevelSet f' c)] :
    @HasGroupoid K _ (affineLevelSet f' c) _ (affineChartedSpace f' c e)
      (contDiffGroupoid ⊤ (modelWithCornersSelf ℝ K)) := by
  letI := affineChartedSpace f' c e
  refine ⟨fun {a a'} ha ha' => ?_⟩
  rw [show a = affineChart f' c e from ha, show a' = affineChart f' c e from ha']
  exact symm_trans_mem_contDiffGroupoid _

instance affineIsManifold [Nonempty (affineLevelSet f' c)] :
    @IsManifold ℝ _ K _ _ K _ (modelWithCornersSelf ℝ K) ⊤
      (affineLevelSet f' c) _ (affineChartedSpace f' c e) :=
  @IsManifold.mk' ℝ _ K _ _ K _ (modelWithCornersSelf ℝ K) ⊤
    (affineLevelSet f' c) _ (affineChartedSpace f' c e) (affineHasGroupoid f' c e)

/-- **The inclusion of the affine level set into `E` is a topological embedding.** -/
theorem affine_isEmbedding_subtypeVal [Nonempty (affineLevelSet f' c)] :
    Topology.IsEmbedding (Subtype.val : affineLevelSet f' c → E) :=
  Topology.IsEmbedding.subtypeVal

/-- **The inclusion of the affine level set into `E` is `C^∞`.** This is the smooth-embedding property:
the level set, as a manifold over the fixed codim-1 model `K`, includes smoothly into `E` (modelled on
itself). In the single global chart the inclusion reads `k ↦ x₀ + e k`, an affine map — hence `C^∞`. -/
theorem affine_contMDiff_subtypeVal [Nonempty (affineLevelSet f' c)] :
    haveI := affineChartedSpace f' c e
    ContMDiff (modelWithCornersSelf ℝ K) (modelWithCornersSelf ℝ E) ⊤
      (fun x : ↥(affineLevelSet f' c) => (x : E)) := by
  letI := affineChartedSpace f' c e
  refine contMDiff_iff.mpr ⟨continuous_subtype_val, ?_⟩
  intro x y
  rw [extChartAt_self_eq]
  simp only [modelWithCornersSelf_coe, Function.id_comp]
  apply ContDiffOn.congr
    (f := fun k : K => affineBasePoint f' c + ((LinearMap.ker (f' : E →ₗ[ℝ] ℝ)).subtypeL (e k)))
  · exact (contDiff_const.add ((LinearMap.ker
      (f' : E →ₗ[ℝ] ℝ)).subtypeL.contDiff.comp e.contDiff)).contDiffOn
  · intro k _
    show (((extChartAt 𝓘(ℝ, K) x).symm k : ↥(affineLevelSet f' c)) : E)
      = affineBasePoint f' c + ((LinearMap.ker (f' : E →ₗ[ℝ] ℝ)).subtypeL (e k))
    rw [extChartAt_coe_symm]
    simp only [modelWithCornersSelf_coe_symm, Function.comp_id]
    exact affineChart_symm_apply f' c e k

end Affine

/-!
## Euclidean-model corollary (finite-dimensional affine submersion)

For a finite-dimensional `E`, the abstract model `K` of the affine level set can be instantiated as the
genuine Euclidean space `EuclideanSpace ℝ (Fin (finrank ℝ (ker f')))` of the right (codim-1) dimension,
via Mathlib's `toEuclidean : ker f' ≃L EuclideanSpace ℝ (Fin (finrank ℝ (ker f')))`. This is the
textbook statement "the level set is a smooth manifold modelled on Euclidean space".
-/

section EuclideanModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (f' : E →L[ℝ] ℝ) (c : ℝ)

/-- The fixed Euclidean model for the affine level set: `EuclideanSpace ℝ (Fin (finrank ℝ (ker f')))`,
of dimension `finrank E - 1` (by `SmithTransversality.submersion_ker_codim_one` when `f'` is onto). -/
abbrev euclideanModel : Type :=
  EuclideanSpace ℝ (Fin (Module.finrank ℝ (LinearMap.ker (f' : E →ₗ[ℝ] ℝ))))

/-- The continuous linear equivalence between the Euclidean model and `ker f'`. -/
noncomputable def euclideanModelEquiv :
    euclideanModel f' ≃L[ℝ] LinearMap.ker (f' : E →ₗ[ℝ] ℝ) :=
  toEuclidean.symm

/-- **The affine level set is a charted space over the Euclidean model.** -/
noncomputable instance euclideanAffineChartedSpace [Nonempty (affineLevelSet f' c)] :
    ChartedSpace (euclideanModel f') (affineLevelSet f' c) :=
  affineChartedSpace f' c (euclideanModelEquiv f')

/-- **The affine level set is a `C^∞` manifold over the Euclidean model**
`EuclideanSpace ℝ (Fin (finrank ℝ (ker f')))` — the textbook "smooth manifold modelled on `ℝⁿ⁻¹`". -/
instance euclideanAffineIsManifold [Nonempty (affineLevelSet f' c)] :
    @IsManifold ℝ _ (euclideanModel f') _ _ (euclideanModel f') _
      (modelWithCornersSelf ℝ (euclideanModel f')) ⊤ (affineLevelSet f' c) _
      (euclideanAffineChartedSpace f' c) :=
  affineIsManifold f' c (euclideanModelEquiv f')

/-- **The inclusion of the Euclidean-modelled affine level set into `E` is `C^∞`.** -/
theorem euclidean_affine_contMDiff_subtypeVal [Nonempty (affineLevelSet f' c)] :
    haveI := euclideanAffineChartedSpace f' c
    ContMDiff (modelWithCornersSelf ℝ (euclideanModel f')) (modelWithCornersSelf ℝ E) ⊤
      (fun x : ↥(affineLevelSet f' c) => (x : E)) :=
  affine_contMDiff_subtypeVal f' c (euclideanModelEquiv f')

end EuclideanModel

end SKEFTHawking.SmithRegularValue
