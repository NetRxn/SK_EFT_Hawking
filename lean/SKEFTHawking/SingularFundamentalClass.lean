import Mathlib
import SKEFTHawking.SingularManifoldFundamentalClass
import SKEFTHawking.SingularRelativeEmpty
import SKEFTHawking.SingularGoodCompactManifold

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

/-- **Restriction of an absolute class to the local homology over a set** `ρ_K : Hₙ(M) → Hₙ(M | K)`,
the composite `Hₙ(M) ≅ Hₙ(M, ∅) → Hₙ(M, M∖K)`. Factors `restrictHomologyToPoint y` for `y ∈ K`
(`restrictToPoint_restrictHomologyToSet`). -/
noncomputable def restrictHomologyToSet {X : TopCat} (K : Set ↑X) (n : ℕ) :
    Homology X n →ₗ[ZMod 2] RelativeHomology (Kᶜ : Set ↑X) n :=
  (relIncl (Set.empty_subset (Kᶜ : Set ↑X)) n).comp
    (relHomologyEmptyEquiv (X := X) n).symm.toLinearMap

/-- **Restriction to a set then to a point equals restriction to the point**: for `y ∈ K`,
`restrictToPoint hy ∘ ρ_K = ρ_y` (functoriality of `relIncl`, `relIncl_trans`). The factoring that
lets the per-point restriction value of `α` be read off the single class `ρ_K α ∈ Hₙ(M|K)`. -/
theorem restrictToPoint_restrictHomologyToSet {X : TopCat} {K : Set ↑X} {y : ↑X} (hy : y ∈ K)
    (n : ℕ) (α : Homology X n) :
    SKEFTHawking.SingularManifoldFundamentalClass.restrictToPoint hy n
        (restrictHomologyToSet K n α)
      = restrictHomologyToPoint y n α := by
  show relIncl (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hy)) n
      (relIncl (Set.empty_subset (Kᶜ : Set ↑X)) n ((relHomologyEmptyEquiv (X := X) n).symm α))
    = relIncl (Set.empty_subset ({y}ᶜ : Set ↑X)) n ((relHomologyEmptyEquiv (X := X) n).symm α)
  rw [relIncl_trans]

/-! ### `setOf`-form local restrictions (matching `manifoldLocalIso`'s domain syntactically)

`manifoldLocalIso x`'s domain is `RelativeHomology {y | y ≠ x}` (the `setOf` form, baked through the
committed chart bridge). Composing `restrictToPoint`/`restrictHomologyToPoint` (which land in the
**compl** form `{x}ᶜ`) with it forces the unifier to reduce `{x}ᶜ → {y | y ≠ x}` through the heavy
`RelativeHomology` quotient on *every* comparison — a 200k-heartbeat `isDefEq` wall (the two forms are
`rfl`-equal in isolation but lethal in the machinery). These `Ne`-variants land in the **`setOf`** form
syntactically, so the local-constancy composition is defeq-free. Each is `rfl`-equal to its compl-form
sibling (`{z | z ≠ x} = {x}ᶜ`), bridging to the rest of the finale cheaply at the `relIncl` level. -/

/-- `setOf`-form `ρₓ` — `restrictHomologyToPoint` landing in `{z | z ≠ x}` (= `{x}ᶜ`). -/
noncomputable def restrictHomologyToPointNe {X : TopCat} (x : ↑X) (n : ℕ) :
    Homology X n →ₗ[ZMod 2] RelativeHomology ({z | z ≠ x} : Set ↑X) n :=
  (relIncl (Set.empty_subset ({z | z ≠ x} : Set ↑X)) n).comp
    (relHomologyEmptyEquiv (X := X) n).symm.toLinearMap

/-- `setOf`-form restriction-to-a-point `Hₙ(M|K) → Hₙ(M|y)` (`y ∈ K`), landing in `{z | z ≠ y}`. -/
noncomputable def restrictToPointNe {X : TopCat} {K : Set ↑X} {y : ↑X} (hy : y ∈ K) (n : ℕ) :
    RelativeHomology (Kᶜ : Set ↑X) n →ₗ[ZMod 2] RelativeHomology ({z | z ≠ y} : Set ↑X) n :=
  relIncl (show (Kᶜ : Set ↑X) ⊆ {z | z ≠ y} from fun _z hz hzy => hz (hzy.symm ▸ hy)) n

/-- **The `setOf`-form factoring** `restrictToPointNe hy ∘ ρ_K = ρ_yNe` (`relIncl_trans`); the
`Ne`-analogue of `restrictToPoint_restrictHomologyToSet`. All `relIncl`, no `manifoldLocalIso` — so the
`{z|z≠y}` form appears consistently and there is no cross-form defeq. -/
theorem restrictToPointNe_restrictHomologyToSet {X : TopCat} {K : Set ↑X} {y : ↑X} (hy : y ∈ K)
    (n : ℕ) (α : Homology X n) :
    restrictToPointNe hy n (restrictHomologyToSet K n α) = restrictHomologyToPointNe y n α := by
  show relIncl (show (Kᶜ : Set ↑X) ⊆ {z | z ≠ y} from fun _z hz hzy => hz (hzy.symm ▸ hy)) n
      (relIncl (Set.empty_subset (Kᶜ : Set ↑X)) n ((relHomologyEmptyEquiv (X := X) n).symm α))
    = relIncl (Set.empty_subset ({z | z ≠ y} : Set ↑X)) n ((relHomologyEmptyEquiv (X := X) n).symm α)
  rw [relIncl_trans]

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

/-! ## High-degree vanishing of the closed manifold -/

/-- **A closed manifold has no homology above its dimension**: `Hᵢ(M;ℤ/2) = 0` for `i > m+2`. The
absolute version of `goodCompact_univ`'s `vanishAbove (m+2) univ` (`Hᵢ(M | univ) = Hᵢ(M, ∅) = Hᵢ(M)`
via `relHomologyEmptyEquiv`). -/
theorem homology_vanish_above {m : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (i : ℕ) (hi : m + 2 < i)
    (α : Homology (TopCat.of M) i) : α = 0 := by
  have h := (SingularGoodCompactManifold.goodCompact_univ (m := m) (M := M)).1 i hi
  rw [Set.compl_univ] at h
  exact (relHomologyEmptyEquiv (X := TopCat.of M) i).symm.injective
    (by rw [h ((relHomologyEmptyEquiv (X := TopCat.of M) i).symm α), map_zero])

end SKEFTHawking.SingularFundamentalClass
