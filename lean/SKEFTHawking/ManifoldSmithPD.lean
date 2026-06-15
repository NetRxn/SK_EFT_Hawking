/-
# Phase 5q.F — the Poincaré-dual submanifold over a GENERAL manifold base (geometric Smith map, brick 2)

The geometric Smith map `[M⁵] ↦ [PD(a)⁴]` of the Smith-LES discharge sends a closed manifold `M` to the
Poincaré dual `N = PD(a)` = the zero locus of a transverse section of the line bundle `L_a`. For the
Smith map to be a map on `DataBordismGrp` (whose elements are arbitrary `SingularManifold`s), `PD(a)`
must be a `SingularManifold` over an *arbitrary* boundaryless base `M` — not the model space `E`. This
module lifts the model-space `SmithLineBundle.sectionZeroLocus_isManifold` (base `E`) to a general
boundaryless manifold base `M`, using the manifold regular-value theorem
`ManifoldRegularValue.mLevelSetSingularManifold` (brick 1, built + reviewed-GENUINE).

The line-bundle core (`lineBundleCore`, `sectionCoord`, `sectionZeroLocus`, the trivialization-
independence) is already general over any topological base, so this module only supplies the
manifold-base transversality hypothesis and the thin wrappers.

Kernel-pure; no axioms beyond Mathlib's core {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import SKEFTHawking.SmithLineBundle
import SKEFTHawking.ManifoldRegularValue

namespace SKEFTHawking.ManifoldSmithPD

open scoped Manifold
open SKEFTHawking.SmithLineBundle SKEFTHawking.ManifoldRegularValue
open SKEFTHawking.SmithRegularValueGeneral (euclideanModel)

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M] [I.Boundaryless]
  {ι : Type*} (c : SignCocycle M ι)

/-- The **manifold section-transversality** hypothesis: the line-bundle section's coordinate function
`sectionCoord σ : M → ℝ` is a `C^∞` (`ContMDiff`) submersion read in charts — it is `ContMDiff`, and at
every zero the chart-local derivative `fderiv (localRep (sectionCoord σ) p) (extChartAt I p p)` is
surjective. The manifold-base analogue of `SmithLineBundle.SectionTransverse` (the generic-section
input that makes `N = PD(a)` a smooth submanifold, by Thom transversality). -/
structure MSectionTransverse (σ : M → c.TotalSpace) : Prop where
  /-- The section is base-point preserving. -/
  isSection : c.IsSection σ
  /-- The coordinate function is `C^∞` as a manifold map. -/
  contMDiff : ContMDiff I 𝓘(ℝ, ℝ) ⊤ (c.sectionCoord σ)
  /-- The coordinate function is a submersion (read in charts) on its zero locus. -/
  submersion : ∀ p ∈ mZeroLocus (c.sectionCoord σ),
    LinearMap.range (fderiv ℝ (localRep (I := I) (c.sectionCoord σ) p) (extChartAt I p p) :
      E →ₗ[ℝ] ℝ) = ⊤

/-- **`N = PD(a)` is a `C^∞` manifold over a general boundaryless manifold base** — the manifold
regular-value theorem (`ManifoldRegularValue.mLevelSetIsManifold`) applied to a transverse section's
coordinate function. The section zero locus `(sectionCoord σ)⁻¹(0) ⊆ M` is a charted space over the
fixed Euclidean model `EuclideanSpace ℝ (Fin (finrank E − 1))` and a `C^∞` manifold of codimension 1. -/
theorem mSectionZeroLocus_isManifold (σ : M → c.TotalSpace) (h : MSectionTransverse c σ) :
    @IsManifold ℝ _ (euclideanModel E) _ _ (euclideanModel E) _
      (modelWithCornersSelf ℝ (euclideanModel E)) ⊤ (mZeroLocus (c.sectionCoord σ)) _
      (mLevelSetChartedSpace (I := I) (c.sectionCoord σ) h.contMDiff h.submersion) :=
  mLevelSetIsManifold (I := I) (c.sectionCoord σ) h.contMDiff h.submersion

/-- **`N = PD(a)` packaged as a `SingularManifold`** (over `PUnit`) — the form the geometric Smith map
`[M] ↦ [PD(a)]` deposits into `DataBordismGrp`. Requires `M` compact, so the zero locus (closed in the
compact `M`) is compact; boundaryless is automatic from the Euclidean self-model. -/
noncomputable def mSectionZeroLocus_singularManifold [CompactSpace M] (σ : M → c.TotalSpace)
    (h : MSectionTransverse (I := I) c σ) :
    SingularManifold PUnit ⊤ (modelWithCornersSelf ℝ (euclideanModel E)) :=
  mLevelSetSingularManifold (I := I) (c.sectionCoord σ) h.contMDiff h.submersion

end SKEFTHawking.ManifoldSmithPD
