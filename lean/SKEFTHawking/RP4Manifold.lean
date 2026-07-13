import Mathlib
import SKEFTHawking.RP4PointSet

/-!
# Phase 5q.H (W-B opener) — the `k`-generic smooth structure on `ℝP⁴`

`RP4PointSet` gives `ℝP⁴ = S⁴/±` a `ChartedSpace (EuclideanSpace ℝ (Fin 4))` structure by
descending the sphere's stereographic charts along the hemisphere open embeddings
(`rp4Chart x = (chartAt _ x |_{hemi x}).lift_openEmbedding (mk|_{hemi x})`). The existing `rp4SM`
witness sits at `k = 0`, where `IsManifold I 0 M` fires for *any* charted space (the degree-0
`contDiffGroupoid` is the whole continuous groupoid).

This module supplies the **`k`-generic** `IsManifold (𝓡 4) k RP4` (all `k : WithTop ℕ∞`): the
transition between two descended charts `rp4Chart x` and `rp4Chart y` reduces — on the sphere —
to the sphere-chart transition on the disjoint opens `hemi x ∩ hemi y` (deck element `1`) and
`hemi x ∩ hemi (-y)` (deck element `-1`, i.e. the antipodal map). Both are `C^k` because `S⁴` is
`ω`-smooth (`EuclideanSpace.instIsManifoldSphere`) and negation on `ℝ⁵` is `C^k`. Since the
literature target `Ω₄^{Pin⁺} ≅ ℤ/16` is a *smooth-category* statement, this lifts the `ℝP⁴`
witness carrier to the smooth category at `k = ∞`.

Reuses the closed-ball campaign house style (`DiskManifoldSmooth.lean`): explicit `ContDiffOn`
transition classes assembled through `isManifold_of_contDiffOn`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/

open Metric Set
open scoped Manifold RealInnerProductSpace
open SKEFTHawking.RP4PointSet

namespace SKEFTHawking.RP4Manifold

noncomputable section

/-- Ambient `ℝ⁵`. -/
abbrev E5 : Type := EuclideanSpace ℝ (Fin (4 + 1))
/-- Model `ℝ⁴`. -/
abbrev E4 : Type := EuclideanSpace ℝ (Fin 4)

/-- Abbreviation for the sphere's stereographic chart at `x`. -/
noncomputable abbrev Φ (x : S4) : OpenPartialHomeomorph S4 E4 := chartAt E4 x

/-! ### §1. Foundational: `S⁴` is `C^k`-smooth, and the antipodal relation on classes -/

/-- Local dimension fact for `S⁴ ⊆ ℝ⁵`, needed by every `stereographic'` unfold. -/
instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (4 + 1))) = 4 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- `S⁴` is a `C^k` manifold for every regularity `k` (from Mathlib's `ω`-smooth instance). -/
instance isManifold_S4 {k : WithTop ℕ∞} : IsManifold (𝓡 4) k S4 := IsManifold.of_le le_top

/-- The class of a sphere point equals the class of its antipode (deck element `-1`). -/
theorem mk_neg (s : S4) :
    Quotient.mk (MulAction.orbitRel ℤˣ S4) (-s) = Quotient.mk (MulAction.orbitRel ℤˣ S4) s := by
  apply Quotient.sound
  refine ⟨(-1 : ℤˣ), ?_⟩
  apply Subtype.ext
  rw [smul_coe]
  norm_num

/-! ### §2. Bridge: `rp4Chart` in terms of the sphere charts -/

/-- The sphere chart's source is the complement of the antipode of the base point. -/
theorem chartAt_S4_source (x : S4) : (Φ x).source = {-x}ᶜ := stereographic'_source (-x)

/-- Every hemisphere point lies in the base chart's source (the antipode is the excluded pole). -/
theorem hemi_subset_source (x : S4) : hemi x ⊆ (Φ x).source := by
  intro s hs
  rw [chartAt_S4_source, Set.mem_compl_iff, Set.mem_singleton_iff]
  intro hcontra
  have hpos : 0 < ⟪(x : E5), (s : E5)⟫ := hs
  rw [hcontra] at hpos
  have : ((-x : S4) : E5) = -(x : E5) := rfl
  rw [this, inner_neg_right, real_inner_self_eq_norm_sq,
    mem_sphere_zero_iff_norm.mp x.2] at hpos
  norm_num at hpos

/-- Descended-chart value: on the hemisphere, `rp4Chart x ∘ mk = Φ x`. -/
theorem rp4Chart_apply_mk (x : S4) {s : S4} (hs : s ∈ hemi x) :
    rp4Chart x (Quotient.mk (MulAction.orbitRel ℤˣ S4) s) = Φ x s := by
  rw [rp4Chart]
  rw [show Quotient.mk (MulAction.orbitRel ℤˣ S4) s
    = (fun y : ↥(hemi x) => Quotient.mk (MulAction.orbitRel ℤˣ S4) y.1) ⟨s, hs⟩ from rfl]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply, OpenPartialHomeomorph.subtypeRestr_coe]
  rfl

/-- The descended chart's source is the image of the hemisphere. -/
theorem rp4Chart_source (x : S4) :
    (rp4Chart x).source = Quotient.mk (MulAction.orbitRel ℤˣ S4) '' hemi x := by
  rw [rp4Chart, OpenPartialHomeomorph.lift_openEmbedding_source,
    OpenPartialHomeomorph.subtypeRestr_source]
  ext p
  constructor
  · rintro ⟨⟨y, hy⟩, hy2, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, hemi_subset_source x hy, rfl⟩

/-- The descended chart's inverse, read on its target, is `mk ∘ Φ x .symm`. -/
theorem rp4Chart_symm_apply (x : S4) {t : E4} (ht : t ∈ (rp4Chart x).target) :
    (rp4Chart x).symm t = Quotient.mk (MulAction.orbitRel ℤˣ S4) ((Φ x).symm t) := by
  have ht' : t ∈ ((Φ x).subtypeRestr (⟨⟨x, mem_hemi_self x⟩⟩ : Nonempty (hemiOpens x))).target := by
    rw [rp4Chart, OpenPartialHomeomorph.lift_openEmbedding_target] at ht; exact ht
  have heq := OpenPartialHomeomorph.subtypeRestr_symm_eqOn (Φ x)
    (⟨⟨x, mem_hemi_self x⟩⟩ : Nonempty (hemiOpens x)) ht'
  rw [Function.comp_apply] at heq
  rw [rp4Chart, OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply, heq]

/-- On the descended chart's target, the sphere-inverse lands in the hemisphere. -/
theorem rp4Chart_symm_mem_hemi (x : S4) {t : E4} (ht : t ∈ (rp4Chart x).target) :
    (Φ x).symm t ∈ hemi x := by
  rw [rp4Chart, OpenPartialHomeomorph.lift_openEmbedding_target] at ht
  have heq := OpenPartialHomeomorph.subtypeRestr_symm_eqOn (Φ x)
    (⟨⟨x, mem_hemi_self x⟩⟩ : Nonempty (hemiOpens x)) ht
  rw [Function.comp_apply] at heq
  rw [heq]
  exact (((Φ x).subtypeRestr (⟨⟨x, mem_hemi_self x⟩⟩ : Nonempty (hemiOpens x))).symm t).2

end

end SKEFTHawking.RP4Manifold
