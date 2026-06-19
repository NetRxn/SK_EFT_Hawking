import Mathlib
import SKEFTHawking.SingularFundamentalClassExist
import SKEFTHawking.PoincareDualityWu

/-!
# Phase 5q.F (w₂-foundation, brick 72c-6) — constructing the Poincaré-duality datum from `[M]`

The `PoincareDualityWu.PoincareDual4Mid` datum (the precise Poincaré-duality requirement the Wu class
consumes) carries three fields: a fundamental-class functional `μ : H⁴ → ℤ/2`, finite-dimensionality of
`H²`, and the non-degeneracy of the middle cup pairing. This module discharges those fields from the
constructed fundamental class `[M]` (`SingularFundamentalClass.fundamentalClass`) and the closed-manifold
Poincaré duality being built in this phase.

**This brick builds `μ = ⟨·, [M]⟩`** — the fundamental-class functional, as the Kronecker pairing of a
top-degree cohomology class against `[M]` (`SingularHomologyMod2.kroneckerH`). The finite-dimensionality
and non-degeneracy fields are the subsequent bricks (the cap product `[M] ⌢ ·` and its Poincaré-duality
iso). Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFundamentalClass

namespace SKEFTHawking.PoincareDualityConstruct

/-- **The fundamental-class functional `μ = ⟨·, [M]⟩ : Hᵐ⁺²(M;ℤ/2) → ℤ/2`** of a closed connected
charted manifold: the Kronecker pairing (`kroneckerH`) of a top-degree cohomology class against the
fundamental class `[M]` (`fundamentalClass`). This is the `PoincareDual4Mid.mu` field (`m = 2`,
`m+2 = 4`); a *constructed* functional, not a hypothesis. -/
noncomputable def fundamentalFunctional {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] :
    Cohomology (TopCat.of M) (m + 2) →ₗ[ZMod 2] ZMod 2 :=
  (kroneckerH (X := TopCat.of M) (m + 2)).flip fundamentalClass

/-- **`μ ω = ⟨ω, [M]⟩`** — the fundamental-class functional evaluates a cohomology class by the
Kronecker pairing against `[M]`. -/
@[simp] theorem fundamentalFunctional_apply {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    (ω : Cohomology (TopCat.of M) (m + 2)) :
    fundamentalFunctional (m := m) (M := M) ω
      = kroneckerH (X := TopCat.of M) (m + 2) ω fundamentalClass :=
  rfl

/-! ### The cap–cup adjunction (toward Poincaré-duality non-degeneracy of the cup pairing) -/

/-- **Cap–cup adjunction** `⟨a ∪ b, c⟩ = ⟨b, a ⌢ c⟩` (chain level): the Kronecker pairing of a cup
product against a chain equals the pairing of the right factor against the cap product. Both sides use
the same Alexander–Whitney front/back split (`a` evaluated on the front `k`-face, `b`/the chain on the
back `l`-face), so on a basis simplex both equal `a(frontₖσ) · b(backₗσ)`. This is the algebraic bridge
from the cup pairing `(a,b) ↦ ⟨a∪b, [M]⟩` to the cap-with-`[M]` duality map — the route to the
`PoincareDual4Mid.nondeg` field once cap descends to homology and `[M] ⌢ ·` is shown to be an iso. -/
theorem kronecker_cup_cap {X : TopCat} {k l : ℕ} (a : SingularCochain X k) (b : SingularCochain X l)
    (c : SingularChain X (k + l)) :
    kronecker (cup a b) c = kronecker b (cap a c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp [map_zero]
  | add c d hc hd =>
      rw [kronecker_add_right, map_add, kronecker_add_right, hc, hd]
  | single σ s =>
      rw [cap_single_smul, capBasis, kronecker_single, kronecker_smul_right, kronecker_smul_right,
        kronecker_single, cup_apply]
      simp only [smul_eq_mul]; ring

end SKEFTHawking.PoincareDualityConstruct
