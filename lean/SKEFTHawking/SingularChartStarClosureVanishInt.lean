/-
# The star-complement chart vanishing, with `IsClosed K` relaxed to `closure K ⊆ U`

`SingularFlatDiskChartVanishInt.relHomology_chartStar_eq_zero` proves
`Hⱼ₊₂(M, M ∖ K; ℤ) = 0` for a set `K` that a chart carries onto a star-shaped body strictly inside
the unit ball of `ℝᵐ⁺¹` — but it asks for `K` (and its chart image `C`) to be **closed**.

That hypothesis is stronger than the proof needs. Both excision steps go through
`SingularManifoldFundamentalClass.cover_compl_open`, whose only real content is

> `interior Kᶜ ∪ V = univ`, i.e. `closure K ⊆ V`,

since `interior Kᶜ = (closure K)ᶜ`. Closedness of `K` is merely the convenient way to get
`closure K = K ⊆ V`. This module states the cover fact in its honest form and re-derives the whole
chain (`openSetExcisionEquivClosureInt` → `chartLocalHomologyEquivClosureInt` →
`relHomology_chartStar_closure_eq_zero`) from it.

The relaxation is load-bearing downstream: the natural cores appearing in a
`{fiberNorm ≥ 1/2}`-relative decomposition are **half-open** (closed in the base coordinate, open in
the fiber coordinate, because the fiber bound is inherited from the *complement* of a closed
sublevel set). Such a core is not closed, but its closure is still a compact body inside the chart —
exactly the hypothesis below. `StarInBall` itself never asked for closedness.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularFlatDiskChartVanishInt

open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularExcisionIsoInt (excisionEquivInt)
open SKEFTHawking.SingularStarComplementRetractInt
open SKEFTHawking.SingularChartTransportInt (chartPairEquiv_setInt)

namespace SKEFTHawking.SingularChartStarClosureVanishInt

variable {X : TopCat}

/-! ## §1. The excision cover, stated with the closure -/

/-- **The honest cover fact behind open-set excision.** `interior Kᶜ = (closure K)ᶜ`, so the two
interiors cover as soon as `closure K ⊆ V`; closedness of `K` is not needed. -/
theorem cover_compl_open_closure {K : Set ↑X} {V : Set ↑X} (hV : IsOpen V)
    (hKV : closure K ⊆ V) :
    (⋃ U ∈ ({Kᶜ, V} : Set (Set ↑X)), interior U) = Set.univ := by
  rw [Set.biUnion_pair, hV.interior_eq, interior_compl, Set.eq_univ_iff_forall]
  intro x
  by_cases h : x ∈ closure K
  · exact Or.inr (hKV h)
  · exact Or.inl h

/-- **Integral open-set excision, closure form**: `Hₙ₊₁(V, V∖K; ℤ) ≅ Hₙ₊₁(X, X∖K; ℤ)` whenever `V` is
open and `closure K ⊆ V`. Generalises `SingularChartTransportInt.openSetExcisionEquivInt` (which
takes `IsClosed K` and `K ⊆ V`). -/
noncomputable def openSetExcisionEquivClosureInt {K : Set ↑X} {V : Set ↑X} (hV : IsOpen V)
    (hKV : closure K ⊆ V) (n : ℕ) :
    RelHomologyInt (restr Kᶜ V) (n + 1) ≃ₗ[ℤ] RelHomologyInt Kᶜ (n + 1) :=
  excisionEquivInt Kᶜ V n (cover_compl_open_closure hV hKV)

/-! ## §2. Chart transport and the vanishing -/

/-- **The chart-transport equivalence for a chart-supported core**, with `closure`-hypotheses:
`Hⱼ₊₂(M, M∖K; ℤ) ≅ Hⱼ₊₂(ℝᵐ⁺¹, ℝᵐ⁺¹∖C; ℤ)` when a chart `e : U ≃ₜ V` matches `K` with `C` and both
closures stay inside their chart domains. -/
noncomputable def chartLocalHomologyEquivClosureInt {M : TopCat} {m : ℕ}
    {K : Set ↑M} {U : Set ↑M} (hU : IsOpen U) (hKU : closure K ⊆ U)
    {C : Set ↑(Eucl (m + 1))} {V : Set ↑(Eucl (m + 1))} (hV : IsOpen V) (hCV : closure C ⊆ V)
    (e : ↥U ≃ₜ ↥V) (hcompat : ∀ u : ↥U, ((e u : ↑(Eucl (m + 1))) ∈ C) ↔ (u : ↑M) ∈ K)
    (j : ℕ) :
    RelHomologyInt Kᶜ (j + 2) ≃ₗ[ℤ] RelHomologyInt Cᶜ (j + 2) :=
  ((openSetExcisionEquivClosureInt hU hKU (j + 1)).symm.trans
    (chartPairEquiv_setInt e hcompat (j + 2))).trans
      (openSetExcisionEquivClosureInt hV hCV (j + 1))

/-- **`Hⱼ₊₂(M, M ∖ K; ℤ) = 0` for a chart-supported star-shaped core** (`j + 2 ≤ m`), with `K` only
required to have its closure inside the chart domain.

At `m = 3`, `j ∈ {0, 1}`: `H₂(M|K) = H₃(M|K) = 0` for any `K` that a `4`-chart carries onto a
star-shaped body strictly inside the unit ball of `ℝ⁴` — **including half-open bodies** such as
`{‖z‖ ≤ r} × {‖w‖ < s}`, which `SingularFlatDiskChartVanishInt.relHomology_chartStar_eq_zero`
cannot reach. -/
theorem relHomology_chartStar_closure_eq_zero {M : TopCat} {m : ℕ}
    {K : Set ↑M} {U : Set ↑M} (hU : IsOpen U) (hKU : closure K ⊆ U)
    {C : Set ↑(Eucl (m + 1))} {V : Set ↑(Eucl (m + 1))} (hV : IsOpen V) (hCV : closure C ⊆ V)
    (e : ↥U ≃ₜ ↥V) (hcompat : ∀ u : ↥U, ((e u : ↑(Eucl (m + 1))) ∈ C) ↔ (u : ↑M) ∈ K)
    (hstar : StarInBall C) (j : ℕ) (hj : j + 2 ≤ m) (x : RelHomologyInt Kᶜ (j + 2)) : x = 0 := by
  refine (chartLocalHomologyEquivClosureInt hU hKU hV hCV e hcompat j).injective ?_
  rw [map_zero]
  exact relHomology_compl_eq_zero hstar j hj _

end SKEFTHawking.SingularChartStarClosureVanishInt
