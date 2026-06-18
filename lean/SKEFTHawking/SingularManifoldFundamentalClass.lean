import Mathlib
import SKEFTHawking.SingularPairLES
import SKEFTHawking.SingularRelativeMV
import SKEFTHawking.SingularChartBridge

/-!
# Phase 5q.F (w₂-foundation, brick 6e) — toward the fundamental class `[M]`

Building `Hₙ(M; ℤ/2) ≅ ℤ/2` for a closed `n`-manifold (Hatcher Lemma 3.27) on this phase's hand-rolled
singular ℤ/2 homology. The engine is the relative Mayer–Vietoris LES (`SingularRelativeMV`); the local
input is `Hₙ(M | x) ≅ ℤ/2` (`SingularChartBridge.manifoldLocalIso`). This file collects the
pair-LES reductions and the compactness induction.

First brick: the **pair-LES connecting isomorphism for an acyclic ambient**
`Hₙ₊₁(X, A) ≅ Hₙ(A)` when `Hₙ₊₁(X) = Hₙ(X) = 0` — the reduction `Hₙ(ℝⁿ, ℝⁿ∖A) ≅ H̃ₙ₋₁(ℝⁿ∖A)` used in the
convex base case. Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularPairLES

namespace SKEFTHawking.SingularManifoldFundamentalClass

variable {X : TopCat}

/-- **The pair-LES connecting map is an isomorphism over an acyclic ambient**: if `Hₙ₊₁(X) = 0` and
`Hₙ(X) = 0`, then `δ : Hₙ₊₁(X, A) → Hₙ(A)` is bijective. (Injective: `ker δ = range j_* = 0` since
`Hₙ₊₁(X) = 0`. Surjective: `range δ = ker i_* = ⊤` since `Hₙ(X) = 0`.) The reduction
`Hₙ(ℝⁿ, ℝⁿ∖A) ≅ Hₙ₋₁(ℝⁿ∖A)`. -/
theorem connecting_bijective_of_acyclic (S : Set ↑X) (n : ℕ)
    (h1 : ∀ x : Homology X (n + 1), x = 0) (h0 : ∀ x : Homology X n, x = 0) :
    Function.Bijective (connecting S n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, hy⟩ := (exact_homProj_connecting S n x).mp hx
    rw [← hy, h1 y, map_zero]
  · intro y
    exact (exact_connecting_homIncl S n y).mp (h0 _)

/-- The acyclic-ambient connecting isomorphism `Hₙ₊₁(X, A) ≃ₗ Hₙ(A)`. -/
noncomputable def connectingEquiv_of_acyclic (S : Set ↑X) (n : ℕ)
    (h1 : ∀ x : Homology X (n + 1), x = 0) (h0 : ∀ x : Homology X n, x = 0) :
    RelativeHomology S (n + 1) ≃ₗ[ZMod 2] Homology (sub S) n :=
  LinearEquiv.ofBijective (connecting S n) (connecting_bijective_of_acyclic S n h1 h0)

end SKEFTHawking.SingularManifoldFundamentalClass
