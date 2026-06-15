/-
# Phase 5q.F W4-cohomology brick 6 — the cellular ℤ/2 cup product (toward the intersection form)

The genuine **cup product** on cellular ℤ/2 cohomology — the ring structure that Mathlib lacks entirely
(confirmed: no cup product / cohomology ring in Mathlib, only abstract `CommRing`/`Coalgebra`). It is the
prerequisite for the **intersection form** on `H²` (resp. `H¹` of a surface), which carries the
`ZMod 4`-quadratic refinement underlying the Guillou–Marin / ABK invariant `β` of a Pin⁺ 4-manifold.

The cup product is NOT determined by the chain complex alone — it needs a **diagonal approximation**
`Δ : C → C ⊗ C` (Alexander–Whitney). We carry the diagonal as data (`CupData.coeff`, the ℤ/2
coefficients of the cellular diagonal), exactly as the project carries Stiefel–Whitney data on
`HasStiefelWhitney`; the cochain cup product, its bilinearity, and (with the `leibniz` chain-map field)
its descent to cohomology are then genuine theorems. This module ships the **cochain-level** cup product
and its bilinearity; the Leibniz/descent and the surface intersection form follow in the next bricks.

Per Invariant #15: no new axioms — `CupData` is carried geometric structure (the diagonal), and the cup
product is a definitional construction over it.
-/
import SKEFTHawking.CellularCohomologyMod2

namespace SKEFTHawking.CellularCohomologyMod2

open scoped BigOperators

/-- **Diagonal-approximation data** on a cell complex `C` (carried, as `HasStiefelWhitney` carries SW
data): `coeff p q σ a b` is the ℤ/2 coefficient of `(a : p-cell) ⊗ (b : q-cell)` in the cellular
diagonal `Δσ` of the `(p+q)`-cell `σ` (the Alexander–Whitney diagonal). It determines the cup product on
cochains. -/
structure CupData (C : CellComplex) where
  /-- The diagonal coefficient of `a ⊗ b` in `Δσ`. -/
  coeff : (p q : ℕ) → C.cells (p + q) → C.cells p → C.cells q → ZMod 2

namespace CupData

variable {C : CellComplex} (D : CupData C)

/-- The **cochain cup product** `⌣ : Cᵖ × Cᵍ → Cᵖ⁺ᵍ`, `(f ⌣ g)(σ) = ∑_{a,b} ⟨Δσ : a⊗b⟩ · f(a) · g(b)`,
induced by the carried diagonal. -/
def cup {p q : ℕ} (f : Cochain C p) (g : Cochain C q) : Cochain C (p + q) :=
  fun σ => ∑ a : C.cells p, ∑ b : C.cells q, D.coeff p q σ a b * f a * g b

@[simp] theorem cup_apply {p q : ℕ} (f : Cochain C p) (g : Cochain C q) (σ : C.cells (p + q)) :
    D.cup f g σ = ∑ a : C.cells p, ∑ b : C.cells q, D.coeff p q σ a b * f a * g b := rfl

/-- The cup product is **left-additive**. -/
theorem cup_add_left {p q : ℕ} (f₁ f₂ : Cochain C p) (g : Cochain C q) :
    D.cup (f₁ + f₂) g = D.cup f₁ g + D.cup f₂ g := by
  funext σ
  simp only [cup_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- The cup product is **right-additive**. -/
theorem cup_add_right {p q : ℕ} (f : Cochain C p) (g₁ g₂ : Cochain C q) :
    D.cup f (g₁ + g₂) = D.cup f g₁ + D.cup f g₂ := by
  funext σ
  simp only [cup_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- The cup product is **left ℤ/2-linear in the scalar**. -/
theorem cup_smul_left {p q : ℕ} (c : ZMod 2) (f : Cochain C p) (g : Cochain C q) :
    D.cup (c • f) g = c • D.cup f g := by
  funext σ
  simp only [cup_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- The cup product is **right ℤ/2-linear in the scalar**. -/
theorem cup_smul_right {p q : ℕ} (c : ZMod 2) (f : Cochain C p) (g : Cochain C q) :
    D.cup f (c • g) = c • D.cup f g := by
  funext σ
  simp only [cup_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- The cup product is **bilinear**, packaged as a `ZMod 2`-bilinear map `Cᵖ →ₗ Cᵍ →ₗ Cᵖ⁺ᵍ`. -/
def cupₗ {p q : ℕ} : Cochain C p →ₗ[ZMod 2] Cochain C q →ₗ[ZMod 2] Cochain C (p + q) :=
  LinearMap.mk₂ (ZMod 2) (fun f g => D.cup f g)
    (fun f₁ f₂ g => D.cup_add_left f₁ f₂ g) (fun c f g => D.cup_smul_left c f g)
    (fun f g₁ g₂ => D.cup_add_right f g₁ g₂) (fun c f g => D.cup_smul_right c f g)

@[simp] theorem cupₗ_apply {p q : ℕ} (f : Cochain C p) (g : Cochain C q) :
    D.cupₗ f g = D.cup f g := rfl

end CupData

end SKEFTHawking.CellularCohomologyMod2
