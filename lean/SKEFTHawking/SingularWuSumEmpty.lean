/-
# Phase 5q.H (W-A arm 4, hchar step 1) — μ-additivity over a disjoint union with an EMPTY summand

`SingularWuSum.mu_sum` splits `μ_{M⊕N}` when BOTH summands are nonempty (both components'
fundamental classes exist). The `hchar` characteristic-surface tie needs the degenerate variants:
when one summand is empty, the disjoint union's fundamental class IS the surviving component's
pushforward, so `μ` restricts cleanly:

* `fundamentalClass_sum_empty_right/left` — `[M ⊕ ∅] = inl₊[M]` (resp. `[∅ ⊕ N] = inr₊[N]`), by
  the F4 uniqueness machinery: the empty summand contributes no points (its case is `isEmptyElim`)
  and the surviving summand restricts to the local generator along the open embedding
  (`restrict_map_fundClass_openEmbedding`).
* `mu_sum_empty_right/left` — `μ_{M⊕N}(w) = μ_M(inl* w)` (resp. `= μ_N(inr* w)`), through the F3
  Kronecker adjunction.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularFundamentalClassSum
import SKEFTHawking.SingularWuSum

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularCohomologyFunctoriality SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularFundamentalClassPushforward
open SKEFTHawking.PoincareDualityConstruct SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.SingularCochainGlue SKEFTHawking.SingularFundamentalClassSum

namespace SKEFTHawking.SingularWuSumEmpty

section FundClass

variable {m : ℕ} {M N : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
  [TopologicalSpace N] [T2Space N] [CompactSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) N]

/-- **The fundamental class of `M ⊕ ∅` is the pushforward of `[M]`** — the empty summand
contributes no points, and `inl₊[M]` restricts to the local generator at every `inl x`
(open-embedding transport); F4 uniqueness closes. -/
theorem fundamentalClass_sum_empty_right [Nonempty M] [IsEmpty N] :
    fundamentalClass (m := m) (M := M ⊕ N)
      = Homology.map (inlC M N) (m + 2) (fundamentalClass (m := m) (M := M)) := by
  refine (eq_fundamentalClass_of_restricts_generator (fun z => ?_)).symm
  cases z with
  | inl x =>
      rw [show (Sum.inl x : M ⊕ N) = (inlC M N) x from rfl,
        restrict_map_fundClass_openEmbedding (inlC M N) Topology.IsOpenEmbedding.inl x]
  | inr y => exact isEmptyElim y

/-- **The fundamental class of `∅ ⊕ N` is the pushforward of `[N]`** — the mirror. -/
theorem fundamentalClass_sum_empty_left [IsEmpty M] [Nonempty N] :
    fundamentalClass (m := m) (M := M ⊕ N)
      = Homology.map (inrC M N) (m + 2) (fundamentalClass (m := m) (M := N)) := by
  refine (eq_fundamentalClass_of_restricts_generator (fun z => ?_)).symm
  cases z with
  | inl x => exact isEmptyElim x
  | inr y =>
      rw [show (Sum.inr y : M ⊕ N) = (inrC M N) y from rfl,
        restrict_map_fundClass_openEmbedding (inrC M N) Topology.IsOpenEmbedding.inr y]

end FundClass

section Mu

variable {M N : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
  [TopologicalSpace N] [T2Space N] [CompactSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) N]

/-- **μ-restriction over an empty right summand**: `μ_{M⊕N}(w) = μ_M(inl* w)` — the Kronecker
adjunction through `[M ⊕ ∅] = inl₊[M]`. -/
theorem mu_sum_empty_right [Nonempty M] [IsEmpty N] (w : Cohomology (TopCat.of (M ⊕ N)) 4) :
    (poincareDual4Mid_of_closed (M := M ⊕ N)).mu w
      = (poincareDual4Mid_of_closed (M := M)).mu (cohomologyPullback (inlC M N) 4 w) := by
  show kroneckerH (X := TopCat.of (M ⊕ N)) (2 + 2) w (fundamentalClass (m := 2) (M := M ⊕ N))
    = kroneckerH (X := TopCat.of M) (2 + 2) (cohomologyPullback (inlC M N) (2 + 2) w)
        (fundamentalClass (m := 2) (M := M))
  rw [kroneckerH_cohomologyPullback, ← fundamentalClass_sum_empty_right (m := 2)]

/-- **μ-restriction over an empty left summand**: `μ_{M⊕N}(w) = μ_N(inr* w)` — the mirror. -/
theorem mu_sum_empty_left [IsEmpty M] [Nonempty N] (w : Cohomology (TopCat.of (M ⊕ N)) 4) :
    (poincareDual4Mid_of_closed (M := M ⊕ N)).mu w
      = (poincareDual4Mid_of_closed (M := N)).mu (cohomologyPullback (inrC M N) 4 w) := by
  show kroneckerH (X := TopCat.of (M ⊕ N)) (2 + 2) w (fundamentalClass (m := 2) (M := M ⊕ N))
    = kroneckerH (X := TopCat.of N) (2 + 2) (cohomologyPullback (inrC M N) (2 + 2) w)
        (fundamentalClass (m := 2) (M := N))
  rw [kroneckerH_cohomologyPullback, ← fundamentalClass_sum_empty_left (m := 2)]

end Mu

end SKEFTHawking.SingularWuSumEmpty
