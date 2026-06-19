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

end SKEFTHawking.PoincareDualityConstruct
