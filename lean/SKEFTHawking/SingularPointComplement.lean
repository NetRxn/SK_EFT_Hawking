import Mathlib
import SKEFTHawking.SingularChartBridge

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD4f-pc) — the named point-complement set

A **named** definition `pointComplement x := {y | y ≠ x}` for the deleted-point set `M ∖ {x}`, plus the
local-homology iso `manifoldLocalIso` repackaged over it (`manifoldLocalIsoPC`).

**Why this exists (the elaboration-wall fix).** The local Poincaré-duality assembly equates a relative
homology class built over a *freshly written* `{y | y ≠ x}` against `(manifoldLocalIso x).symm 1`, whose
type carries `manifoldLocalIso`'s *own* `{y | y ≠ x}`. Comparing two `{y | y ≠ x}` elaborated in different
contexts (the `x : ↑(TopCat.of M)` vs `x : M` coercion-path mismatch) unfolds `RelativeHomology` to its
quotient and grinds past the heartbeat limit. Routing everything through the *single named term*
`pointComplement x` collapses every such comparison to `pointComplement x =?= pointComplement x` (`rfl`),
so the wall never forms. The wrapper `manifoldLocalIsoPC` is the seam: it absorbs the one unavoidable
`pointComplement x =?= {y | y ≠ x}` unification here (isolated, well under budget), and downstream code
sees only the named set.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularChartBridge

namespace SKEFTHawking.SingularPointComplement

/-- **The point-complement set** `M ∖ {x} = {y | y ≠ x}`, as a named `Set ↑(TopCat.of M)`. Giving it a
stable name keeps every downstream relative-(co)homology comparison at `pointComplement x =?= pointComplement x`
(`rfl`), dodging the cross-context `{y | y ≠ x}` coercion heartbeat wall. -/
def pointComplement {m : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (x : M) : Set ↑(TopCat.of M) :=
  {y | y ≠ x}

/-- **The local homology iso over the named set**: `Hₘ₊₂(M, M∖x) ≅ ℤ/2`, repackaged over
`pointComplement x` (definitionally `SingularChartBridge.manifoldLocalIso x`). The seam absorbing the one
`pointComplement x =?= {y | y ≠ x}` unification, isolated here within budget. -/
noncomputable def manifoldLocalIsoPC {m : ℕ} {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (x : M) :
    RelativeHomology (X := TopCat.of M) (pointComplement (m := m) x) (m + 2) ≃ₗ[ZMod 2] ZMod 2 :=
  manifoldLocalIso x

end SKEFTHawking.SingularPointComplement
