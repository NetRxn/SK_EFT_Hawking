import Mathlib
import SKEFTHawking.SingularOpenDuality
import SKEFTHawking.SingularCSCConvexChart
import SKEFTHawking.SingularConvexSubAcyclic

/-!
# Phase 5q.G (G1 PD-induction, base-case B6 upper conjuncts) — chart-convex duality is bijective
in the middle window

For a chart-convex open `W` and any window degree `2 ≤ k < m+2` with positive target degree,
`D_W : Hᵏ_c(W) → H_{m'+1}(sub W)` is a bijection **between trivial modules**: the CSC side
vanishes by B3 (`cscOpen_eq_zero_of_chartConvex`) and the homology side by B5
(`homology_chartConvexSub_eq_zero`). The statement is `z₀`-presentation-agnostic — any duality
presentation (native or `castChain`-junctioned) of any ambient cycle is covered, so the base
case never pays a `castChain` junction.

At the deg-4 window (`m = 2`) this covers the `(k, m') = (2, 1)` and `(3, 0)` conjuncts of the
induction predicate `P(W) = Bij D@(2,1) ∧ Bij D@(3,0) ∧ Bij D⁰`; the `D⁰` conjunct is B4c
(`openDuality₀_bijective_of_chartConvex`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularCompactlySupportedOpen SKEFTHawking.SingularOpenDuality
open SKEFTHawking.SingularCSCConvexChart SKEFTHawking.SingularConvexSubAcyclic

namespace SKEFTHawking.SingularBaseCaseUpper

/-- A linear map between modules that both vanish identically is a bijection. -/
theorem bijective_of_forall_eq_zero {R A B : Type*} [Semiring R] [AddCommMonoid A]
    [AddCommMonoid B] [Module R A] [Module R B] (f : A →ₗ[R] B)
    (hA : ∀ a : A, a = 0) (hB : ∀ b : B, b = 0) : Function.Bijective f :=
  ⟨fun a b _ => (hA a).trans (hA b).symm,
    fun b => ⟨0, (map_zero f).trans (hB b).symm⟩⟩

/-- **B6 (upper conjuncts): the open duality of a chart-convex open is bijective throughout the
middle window** `2 ≤ k < m+2` (any target degree `m'+1`, any `z₀`-presentation): both sides are
trivial — `Hᵏ_c(W) = 0` (B3) and `H_{m'+1}(sub W) = 0` (B5). -/
theorem openDuality_bijective_of_chartConvex {M : TopCat} [T2Space ↑M] {m : ℕ}
    {U : Set ↑M} (hU : IsOpen U)
    {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))} (hV : IsOpen V)
    (e : ↥U ≃ₜ ↥V)
    {C : Set (EuclideanSpace ℝ (Fin (m + 2)))} (hCconv : Convex ℝ C) (hCopen : IsOpen C)
    {p₀ : EuclideanSpace ℝ (Fin (m + 2))} (hp₀ : p₀ ∈ C) (hCV : C ⊆ V)
    {W : Set ↑M} (hWo : IsOpen W) (hWU : W ⊆ U)
    (hWe : ∀ u : ↥U, (u : ↑M) ∈ W ↔ ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C))
    {k mm : ℕ} (h2 : 2 ≤ k) (hlt : k < m + 2)
    (z₀ : SingularChain M (k + mm + 1)) (hz₀ : chainBoundary M (k + mm) z₀ = 0) :
    Function.Bijective (openDuality (k := k) (m := mm) hWo z₀ hz₀) :=
  bijective_of_forall_eq_zero _
    (fun α => cscOpen_eq_zero_of_chartConvex hU hV e hCconv hCopen ⟨p₀, hp₀⟩ hCV hWU hWe
      h2 hlt α)
    (fun x => homology_chartConvexSub_eq_zero e hCconv hp₀ hCV hWU hWe mm x)

end SKEFTHawking.SingularBaseCaseUpper
