/-
# Phase 5q.H (E1 CSC-PD tower, base-case B6 upper conjuncts) — chart-convex duality is bijective (integral)

Integral (`ZMod 2 → ℤ`) mirror of `SingularBaseCaseUpper.openDuality_bijective_of_chartConvex`: for a
chart-convex open `W` and any window degree `2 ≤ k < m+2` (positive target degree), the open duality
`D_W : Hᵏ_c(W;ℤ) → H_{mm+1}(sub W;ℤ)` is a bijection **between trivial modules** — the CSC side vanishes by
B3 (`cscOpen_eq_zero_of_chartConvexInt`) and the homology side by B5 (`homology_chartConvexSub_eq_zeroInt`).

The `Module.Projective ℤ (relBoundariesInt …)` instance (= infinite-rank Kaplansky) is threaded as `hproj`
into the B3 CSC-vanishing — a true ZFC theorem discharged separately, NOT a posit.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularBaseCaseUpper
import SKEFTHawking.SingularCSCConvexChartInt
import SKEFTHawking.SingularConvexSubAcyclicInt
import SKEFTHawking.SingularOpenDualityInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularOpenDualityInt
open SKEFTHawking.SingularBaseCaseUpper (bijective_of_forall_eq_zero)
open SKEFTHawking.SingularCSCConvexChartInt
open SKEFTHawking.SingularConvexSubAcyclicInt

namespace SKEFTHawking.SingularBaseCaseUpperInt

/-- **B6 (integral, upper conjuncts): the open duality of a chart-convex open is bijective throughout the
middle window** `2 ≤ k < m+2` — both sides trivial (`Hᵏ_c(W;ℤ) = 0` by B3, `H_{mm+1}(sub W;ℤ) = 0` by B5).
Threads `hproj` (the `relBoundariesInt`-projectivity instance) into B3. -/
theorem openDuality_bijective_of_chartConvexInt {M : TopCat} [T2Space ↑M] {m : ℕ}
    (hproj : ∀ (S : Set ↑M) (j : ℕ), Module.Projective ℤ (relBoundariesInt S j))
    {U : Set ↑M} (hU : IsOpen U)
    {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))} (hV : IsOpen V)
    (e : ↥U ≃ₜ ↥V)
    {C : Set (EuclideanSpace ℝ (Fin (m + 2)))} (hCconv : Convex ℝ C) (hCopen : IsOpen C)
    {p₀ : EuclideanSpace ℝ (Fin (m + 2))} (hp₀ : p₀ ∈ C) (hCV : C ⊆ V)
    {W : Set ↑M} (hWo : IsOpen W) (hWU : W ⊆ U)
    (hWe : ∀ u : ↥U, (u : ↑M) ∈ W ↔ ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C))
    {k mm : ℕ} (h2 : 2 ≤ k) (hlt : k < m + 2)
    (z₀ : SingularChainInt M (k + mm + 1)) (hz₀ : chainBoundary M (k + mm) z₀ = 0) :
    Function.Bijective (openDuality (k := k) (m := mm) hWo z₀ hz₀) :=
  bijective_of_forall_eq_zero _
    (fun α => cscOpen_eq_zero_of_chartConvexInt hproj hU hV e hCconv hCopen ⟨p₀, hp₀⟩ hCV hWU hWe
      h2 hlt α)
    (fun x => homology_chartConvexSub_eq_zeroInt e hCconv hp₀ hCV hWU hWe mm x)

end SKEFTHawking.SingularBaseCaseUpperInt
