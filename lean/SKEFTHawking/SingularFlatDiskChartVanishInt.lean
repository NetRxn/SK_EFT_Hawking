import Mathlib
import SKEFTHawking.SingularStarComplementRetractInt
import SKEFTHawking.SingularChartTransportInt

/-!
# The flat-disk local-homology vanishing, transported from the chart model to an ambient space

`SingularStarComplementRetractInt.relHomology_compl_eq_zero` computes
`Hⱼ₊₂(ℝᵐ⁺¹, ℝᵐ⁺¹ ∖ C; ℤ) = 0` (`j + 2 ≤ m`) for `C` a star-shaped body strictly inside the unit
ball — in particular a **closed flat disk**, which has empty interior and so is out of reach of
`SingularConvexComplementRetract`.

This module carries that vanishing across a chart, using the two on-main transport equivalences

* `SingularChartTransportInt.openSetExcisionEquivInt` — `Hₖ(U, U∖K) ≅ Hₖ(M, M∖K)` for `K` closed
  inside the open `U` (the local homology only sees a neighbourhood of `K`), and
* `SingularChartTransportInt.chartPairEquiv_setInt` — `Hₖ(U, U∖K) ≅ Hₖ(V, V∖C)` for a chart
  homeomorphism `e : U ≃ₜ V` matching `K` with `C`,

giving `relHomology_chartStar_eq_zero`:

`Hⱼ₊₂(M, M ∖ K; ℤ) = 0` whenever `K` is a closed set of a space `M` that some chart carries onto a
star-shaped body strictly inside the unit ball of `ℝᵐ⁺¹`, and `j + 2 ≤ m`.

At `m = 3` this reads **`H₂(M|K) = H₃(M|K) = 0` for a flat 2-disk `K` in a 4-chart** — the
per-hemisphere input consumed by `SingularRelativeMVLESInt.localMvDeltaEquivInt`, whose output at
`n = 2` is `H₃(M|A∩B) ≅ H₂(M|A∪B)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularStarComplementRetractInt
open SKEFTHawking.SingularChartTransportInt

namespace SKEFTHawking.SingularFlatDiskChartVanishInt

/-- **The chart-transport equivalence for the local homology of a chart-supported compact**:
`Hⱼ₊₂(M, M∖K; ℤ) ≅ Hⱼ₊₂(ℝᵐ⁺¹, ℝᵐ⁺¹∖C; ℤ)` when a chart `e : U ≃ₜ V` matches the closed `K ⊆ U`
with the closed `C ⊆ V`. Excise into `U`, cross the chart, excise back out of `V`. -/
noncomputable def chartLocalHomologyEquivInt {M : TopCat} {m : ℕ}
    {K : Set ↑M} (hK : IsClosed K) {U : Set ↑M} (hU : IsOpen U) (hKU : K ⊆ U)
    {C : Set ↑(Eucl (m + 1))} (hC : IsClosed C) {V : Set ↑(Eucl (m + 1))} (hV : IsOpen V)
    (hCV : C ⊆ V) (e : ↥U ≃ₜ ↥V) (hcompat : ∀ u : ↥U, ((e u : ↑(Eucl (m + 1))) ∈ C) ↔ (u : ↑M) ∈ K)
    (j : ℕ) :
    RelHomologyInt Kᶜ (j + 2) ≃ₗ[ℤ] RelHomologyInt Cᶜ (j + 2) :=
  ((openSetExcisionEquivInt hK hU hKU (j + 1)).symm.trans
    (chartPairEquiv_setInt e hcompat (j + 2))).trans
      (openSetExcisionEquivInt hC hV hCV (j + 1))

/-- **`Hⱼ₊₂(M, M ∖ K; ℤ) = 0` for a chart-supported star-shaped body** (`j + 2 ≤ m`).

At `m = 3`, `j ∈ {0, 1}`: `H₂(M|K) = H₃(M|K) = 0` for `K` a **closed flat 2-disk** in a 4-chart.
Note the ambient `M` is an arbitrary topological space — only the chart around `K` is used, so this
applies verbatim to a manifold-with-boundary such as a resolution piece `ResE`, provided `K` sits in
an interior chart. -/
theorem relHomology_chartStar_eq_zero {M : TopCat} {m : ℕ}
    {K : Set ↑M} (hK : IsClosed K) {U : Set ↑M} (hU : IsOpen U) (hKU : K ⊆ U)
    {C : Set ↑(Eucl (m + 1))} (hC : IsClosed C) {V : Set ↑(Eucl (m + 1))} (hV : IsOpen V)
    (hCV : C ⊆ V) (e : ↥U ≃ₜ ↥V) (hcompat : ∀ u : ↥U, ((e u : ↑(Eucl (m + 1))) ∈ C) ↔ (u : ↑M) ∈ K)
    (hstar : StarInBall C) (j : ℕ) (hj : j + 2 ≤ m) (x : RelHomologyInt Kᶜ (j + 2)) : x = 0 := by
  refine (chartLocalHomologyEquivInt hK hU hKU hC hV hCV e hcompat j).injective ?_
  rw [map_zero]
  exact relHomology_compl_eq_zero hstar j hj _

/-! ## The concrete 4-dimensional instance -/

/-- **`H₂(M|K) = H₃(M|K) = 0` for a closed flat 2-disk `K` in a 4-chart.** The two degrees are
exactly the per-piece hypotheses of `SingularRelativeMVLESInt.localMvDeltaEquivInt` at `n = 2`, whose
conclusion is `H₃(M | A∩B) ≅ H₂(M | A∪B)`. -/
theorem relHomology_flatDiskChart_four_eq_zero {M : TopCat}
    {K : Set ↑M} (hK : IsClosed K) {U : Set ↑M} (hU : IsOpen U) (hKU : K ⊆ U)
    {V : Set ↑(Eucl 4)} (hV : IsOpen V) (hCV : flatDisk 4 2 (1 / 2) ⊆ V) (e : ↥U ≃ₜ ↥V)
    (hcompat : ∀ u : ↥U, ((e u : ↑(Eucl 4)) ∈ flatDisk 4 2 (1 / 2)) ↔ (u : ↑M) ∈ K)
    (j : ℕ) (hj : j ≤ 1) (x : RelHomologyInt Kᶜ (j + 2)) : x = 0 :=
  relHomology_chartStar_eq_zero (m := 3) hK hU hKU (isClosed_flatDisk 4 2 (1 / 2)) hV hCV e hcompat
    (starInBall_flatDisk 4 2 (by norm_num) (by norm_num)) j (by omega) x

end SKEFTHawking.SingularFlatDiskChartVanishInt
