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

end SKEFTHawking.ManifoldRegularValue
