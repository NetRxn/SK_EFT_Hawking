import Mathlib
import SKEFTHawking.SingularWuSum

/-!
# Phase 5q.G (B-arc, B1) — the Stiefel–Whitney number `w₁⁴[M]` from the Wu tower

The top Stiefel–Whitney number `w₁⁴[M] = ⟨w₁∪w₁∪w₁∪w₁, [M]⟩ ∈ ℤ/2` of a closed charted
4-manifold, built entirely from shipped machinery: `w₁ = v₁` (the first Wu class, degree-4 Wu
identity), the cup tower `H¹×H¹ → H²`, `H²×H² → H⁴`, and the fundamental functional `μ`.

This is the **grade-tying invariant** of the structure-tied Pin⁺ datum (B-arc): on `ℝP⁴` it is
`1` (the generator of the `w₁⁴`-line in `Ω₄^O`), on any null-bordant manifold it is `0` — so
requiring a structure's ABK-grade parity to equal `w₁⁴[M]` makes grade-`0` structures
unpopulatable on `ℝP⁴`, killing the free-grade kernel witness of
`synthetic-grade-ker-bot-nogo`.

Both transport laws are one-rewrite corollaries of the F-ladder:
* **homeo-invariance** (`swNumberW14_pullback`) — F5 μ-transport + F2 cup-compat + F6b
  `wuClass1_pullback`;
* **⊔-additivity** (`swNumberW14_sum`) — `mu_sum` + F2 + `wuClass1_sum_inl/inr`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.PoincareDualityConstruct SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.PoincareDualityWu SKEFTHawking.PoincareDualityWuFormula
open SKEFTHawking.SingularPD4Instances SKEFTHawking.SingularWuTransport
open SKEFTHawking.SingularWuSum SKEFTHawking.SingularCochainGlue

namespace SKEFTHawking.SingularSWNumber

variable {M N : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
  [TopologicalSpace N] [T2Space N] [CompactSpace N] [Nonempty N]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) N]

/-- The first Wu class `v₁ = w₁` of the genuine `(1,3)` PD instance (abbreviation). -/
noncomputable def w1 (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] : Cohomology (TopCat.of M) 1 :=
  wuClass1 (poincareDual4Lo_of_closed (M := M))

/-- **The Stiefel–Whitney number `w₁⁴[M] ∈ ℤ/2`**: `μ((w₁∪w₁) ∪ (w₁∪w₁))` — the top
`w₁`-number of the closed charted 4-manifold, from the genuine Wu tower. -/
noncomputable def swNumberW14 (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] : ZMod 2 :=
  (poincareDual4Mid_of_closed (M := M)).mu (cupH24 (cupH (w1 M) (w1 M)) (cupH (w1 M) (w1 M)))

/-- **`w₁⁴` is a homeomorphism invariant** — the F-ladder transport chain: `v₁` pulls back to
`v₁` (F6b), cup commutes with pullback (F2), and `μ` transports (F5). -/
theorem swNumberW14_homeo_invariant (e : M ≃ₜ N) : swNumberW14 M = swNumberW14 N := by
  show (poincareDual4Mid_of_closed (M := M)).mu
      (cupH24 (cupH (w1 M) (w1 M)) (cupH (w1 M) (w1 M))) = _
  rw [show w1 M = cohomologyPullback (⟨e, e.continuous⟩ :
        C(↑(TopCat.of M), ↑(TopCat.of N))) 1 (w1 N) from (wuClass1_pullback e).symm,
    ← cohomologyPullback_cupH, ← cohomologyPullback_cupH24, mu_pullback e]
  rfl

/-- **`w₁⁴` is additive over disjoint unions** — `mu_sum` + F2 + the `v₁` ⊔-splits (F7d). -/
theorem swNumberW14_sum :
    swNumberW14 (M ⊕ N) = swNumberW14 M + swNumberW14 N := by
  show (poincareDual4Mid_of_closed (M := M ⊕ N)).mu
      (cupH24 (cupH (w1 (M ⊕ N)) (w1 (M ⊕ N))) (cupH (w1 (M ⊕ N)) (w1 (M ⊕ N)))) = _
  rw [mu_sum, cohomologyPullback_cupH24, cohomologyPullback_cupH24, cohomologyPullback_cupH,
    cohomologyPullback_cupH,
    show cohomologyPullback (inlC M N) 1 (w1 (M ⊕ N)) = w1 M from wuClass1_sum_inl,
    show cohomologyPullback (inrC M N) 1 (w1 (M ⊕ N)) = w1 N from wuClass1_sum_inr]
  rfl

end SKEFTHawking.SingularSWNumber
