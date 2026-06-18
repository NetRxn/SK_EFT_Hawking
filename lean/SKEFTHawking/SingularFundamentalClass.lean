import Mathlib
import SKEFTHawking.SingularManifoldFundamentalClass
import SKEFTHawking.SingularRelativeEmpty

/-!
# Phase 5q.F (w₂-foundation, brick 72c-4p) — the [M] finale foundations (Hatcher 3.26)

Foundations for the closed-manifold fundamental class `Hₘ₊₂(M;ℤ/2) ≅ ℤ/2`:

* `restrictHomologyToPoint x` — the restriction `ρₓ : Hₙ(M) → Hₙ(M | x)` of an absolute homology class
  to the local homology at `x`, the composite `Hₙ(M) ≅[relHomologyEmptyEquiv⁻¹] Hₙ(M, ∅) → Hₙ(M, M∖x)`.
* `linearEquiv_zmod2_unique` — over `ℤ/2` there is a **unique** linear iso `V ≃ₗ ℤ/2` (the only nonzero
  scalar is `1`). This is the ℤ/2-coefficient simplification that makes the Hatcher 3.26 local-orientation
  argument elementary: any two identifications of a local homology group with `ℤ/2` agree, so the local
  value `x ↦ (Hₙ(M|x) ≅ ℤ/2)(ρₓ α)` is well-defined and (over a convex chart ball) locally constant.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeMV SKEFTHawking.SingularRelativeEmpty

namespace SKEFTHawking.SingularFundamentalClass

/-- **Restriction of an absolute class to the local homology at a point** `ρₓ : Hₙ(M) → Hₙ(M | x)`:
identify `Hₙ(M) ≅ Hₙ(M, ∅)` (`relHomologyEmptyEquiv`), then include the pair `(M, ∅) → (M, M∖x)`
(`relIncl`, as `∅ ⊆ {x}ᶜ`). The map whose simultaneous behaviour over all `x` detects the fundamental
class. -/
noncomputable def restrictHomologyToPoint {X : TopCat} (x : ↑X) (n : ℕ) :
    Homology X n →ₗ[ZMod 2] RelativeHomology ({x}ᶜ : Set ↑X) n :=
  (relIncl (Set.empty_subset ({x}ᶜ : Set ↑X)) n).comp
    (relHomologyEmptyEquiv (X := X) n).symm.toLinearMap

/-- **Over `ℤ/2` a linear iso to `ℤ/2` is unique**: any two `e₁ e₂ : V ≃ₗ[ZMod 2] ZMod 2` agree, since
the only nonzero element of `ZMod 2` is `1`. The ℤ/2-orientation triviality underlying Hatcher 3.26. -/
theorem linearEquiv_zmod2_unique {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (e₁ e₂ : V ≃ₗ[ZMod 2] ZMod 2) (v : V) : e₁ v = e₂ v := by
  have h0 : (e₁ v = 0) ↔ (e₂ v = 0) := by rw [e₁.map_eq_zero_iff, e₂.map_eq_zero_iff]
  have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hcases (e₁ v) with ha | ha <;> rcases hcases (e₂ v) with hb | hb
  · rw [ha, hb]
  · rw [h0] at ha; rw [ha] at hb; exact absurd hb (by decide)
  · rw [← h0] at hb; rw [hb] at ha; exact absurd ha (by decide)
  · rw [ha, hb]

end SKEFTHawking.SingularFundamentalClass
