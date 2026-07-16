import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinder

/-!
# Phase 5q.H — A CLOPEN COMPONENT IS ITSELF A CLOSED CHARTED MANIFOLD (route (b) step 1)

For the disconnected cylinder datum `D` we peel `M` along a clopen piece `C` and apply the CONNECTED
cylinder engine to `↥C`. This module supplies the manifold structure that makes `↥C` a legitimate
base for `cylW`: a clopen `C ⊆ M` in a closed charted `M` inherits `M`'s charted/manifold structure
(open ⟹ the restricted atlas `TopologicalSpace.Opens.instChartedSpace`; closed ⟹ compactness
inherits). Then `cylW ↥C` is a genuine cylinder and the connected engine applies per piece.

Everything is packaged around `C : TopologicalSpace.Opens M` (an open set), with a hypothesis
`IsClosed (C : Set M)` for the compactness. Mathlib's `Opens.instChartedSpace` gives the charted
structure over the SAME model `EuclideanSpace ℝ (Fin (m' + 2))`; the T2/compact/nonempty facts come
from the subtype instances (`IsClosed.isCompact` on a closed set of a compact space).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom.
-/

open scoped Manifold

namespace SKEFTHawking.PinPlusCylComponentManifold

variable {m' : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

omit [T2Space M] in
/-- **A clopen open-set component is compact**: a closed subset of a compact space is compact, hence
`↥C` is a `CompactSpace`. The `T2Space`/`ChartedSpace (EuclideanSpace ℝ (Fin (m'+2)))` instances on
`↥C` resolve automatically (subtype T2 + `Opens.instChartedSpace`); this closed⟹compact fact is the
only one needing the clopen hypothesis. Together they give `↥C` the closed-charted-manifold instance
stack `cylW` requires, so `cylW ↥C` is a genuine cylinder. -/
theorem isCompact_component (C : TopologicalSpace.Opens M) (hCcl : IsClosed (C : Set M)) :
    CompactSpace (↥C) :=
  isCompact_iff_compactSpace.mp hCcl.isCompact

end SKEFTHawking.PinPlusCylComponentManifold
