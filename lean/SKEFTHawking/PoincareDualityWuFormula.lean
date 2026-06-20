/-
# Phase 5q.F (w₂-tower, L3 layer) — the singular Wu formula `w₂ = v₂ + v₁²`

This module is the **L3 layer** of the Phase 5q.F w₂-tower, built against the Poincaré-duality
DATUM (`PoincareDual4Mid`, and a new degree-`(1,3)` analogue `PoincareDual4Lo`) supplied later by the
L2 core. The goal of the w₂-tower is to derive `w₂` of a closed 4-manifold as a singular-cohomology
invariant via the **Wu formula** `w = Sq(v)`, so the unoriented-bordism floor can be collapsed by
restricting the carrier to Pin⁺ (`w₂ = 0`).

For a closed 4-manifold the Wu formula gives, in `H²(M;ℤ/2)`,

  `w₂ = v₂ + Sq¹ v₁ = v₂ + v₁²`,

because on `H¹` the operation `Sq¹` is the **top square** `x ↦ x ∪ x` (degree-1 = top-square identity).

## What this module BUILDS vs DEFINES (honest scope)

- **`v₁²` ingredient — BUILT.** `cupSquareₗ : H¹ →ₗ[ZMod 2] H²` is the genuine ℤ/2-linear top square
  `x ↦ x ∪ x` on `H¹` (the project's singular `cupSquare`). `sq1_eq_cupSquare_on_H1` records the Wu
  fact `Sq¹ x = x ∪ x` on `H¹` definitionally — the precise sense in which `Sq¹ v₁ = v₁²`.

- **`v₁` (first Wu class) — BUILT against a `(1,3)` PD datum.** `PoincareDual4Lo` is the degree-`(1,3)`
  analogue of `PoincareDual4Mid`: a fundamental-class functional `μ : H⁴→ℤ/2`, an abstract cup pairing
  `cup13 : H¹ →ₗ H³ →ₗ H⁴`, a degree-`(3,4)` cohomology operation `sq1₃ : H³ →ₗ H⁴` (the Bockstein
  `Sq¹` on `H³`, which has NO top-square formula and is carried abstractly — the project has no
  singular Bockstein on `H³`), non-degeneracy `nondeg₁₃` of the `H¹×H³` cup pairing, and the
  Poincaré-duality dimension equality `b₁ = b₃`. From these, `wuClass1` is the PD-dual representative
  of the functional `x ↦ μ(Sq¹ x)` on `H³`, with `wu_relation_v1 : μ(v₁ ∪ x) = μ(Sq¹ x)` for all `x`.

- **The Wu `w₂` class — DEFINED, with its key properties PROVEN.** `wuW2 P P₁₃ := v₂ + v₁²` is the
  singular Wu second class. We do **not** prove `w₂(TM) = v₂ + v₁²` against an abstract tangent-bundle
  Stiefel–Whitney class (the manifold tangent bundle / its SW classes are not in scope here, and not
  in Mathlib for singular manifolds); `wuW2` is DEFINED as `v₂ + v₁²` and documented as the manifold
  `w₂` via the Wu theorem `w = Sq(v)`. Its load-bearing properties are PROVEN: it is the genuine sum
  `v₂ + v₁²` (`wuW2_eq`), and the **Pin⁺ characterization** `w₂ = 0 ↔ v₂ = v₁²` (`wuW2_eq_zero_iff`),
  which is the foundation-collapse criterion the floor-collapse consumes.

All cohomology here is the project's genuine singular ℤ/2 cohomology (`SingularCohomologyMod2`).
Kernel-pure (`{propext, Classical.choice, Quot.sound}`). No new project axiom; no `sorry`.
-/
import Mathlib
import SKEFTHawking.SingularCohomologyMod2
import SKEFTHawking.PoincareDualityWu

namespace SKEFTHawking.PoincareDualityWuFormula

open SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.PoincareDualityWu

variable {X : TopCat}

/-! ### The `v₁²` ingredient: the top square `Sq¹ = (·)²` on `H¹`, as a ℤ/2-linear map -/

/-- The cup square as a **ℤ/2-linear** map `H¹ → H²`: over `ZMod 2` the additive top square
`cupSquare : H¹ → H²` (`cupSquare_add`) is automatically `ZMod 2`-linear (the only scalars are
`0, 1`, and `d * d = d` on `ZMod 2`). This is the genuine `v₁²` ingredient of the Wu formula. -/
noncomputable def cupSquareₗ : Cohomology X 1 →ₗ[ZMod 2] Cohomology X 2 where
  toFun := cupSquare
  map_add' := cupSquare_add
  map_smul' c x := by
    show cupSquare (c • x) = c • cupSquare x
    rw [cupSquare, cupSquare, map_smul, map_smul, LinearMap.smul_apply, smul_smul,
      (by decide : ∀ d : ZMod 2, d * d = d) c]

@[simp] theorem cupSquareₗ_apply (x : Cohomology X 1) : cupSquareₗ x = cupH x x := rfl

/-- **The Wu fact `Sq¹ x = x ∪ x` on `H¹`** (degree-1 = top-square identity): on the top degree of a
1-class, the Steenrod operation `Sq¹` is the cup square. Here this is the project's `cupSquare`,
recorded as the precise meaning of the `v₁²` term in `w₂ = v₂ + Sq¹ v₁ = v₂ + v₁²`. -/
theorem sq1_eq_cupSquare_on_H1 (x : Cohomology X 1) : cupSquareₗ x = cupH x x := rfl

/-! ### The degree-`(1,3)` Poincaré-duality datum and the first Wu class `v₁` -/

/-- A **mod-2 Poincaré-duality datum for a closed 4-manifold at degrees `(1,3)`** — the degree-`(1,3)`
analogue of `PoincareDual4Mid`. It carries:
* a fundamental-class functional `μ : H⁴(X;ℤ/2) → ℤ/2` (`= ⟨·,[M]⟩`),
* the `H¹×H³` **cup pairing** `cup13 : H¹ →ₗ H³ →ₗ H⁴` (abstract: the project's singular cup product
  is currently built only at degrees `(1,1)` and `(2,2)`),
* the degree-`(3,4)` operation `sq1₃ : H³ →ₗ H⁴` — the Bockstein `Sq¹` on `H³` (NO top-square formula;
  carried abstractly, as the project has no singular Bockstein on `H³`),
* `findim₁`, `findim₃` finite-dimensionality of `H¹`, `H³`,
* **Poincaré duality at degrees `(1,3)`**: the non-degeneracy `nondeg₁₃` of the cup pairing (the map
  `H¹ → (H³ →ₗ ZMod 2)`, `a ↦ (b ↦ μ(a ∪ b))`, is injective) together with the PD dimension equality
  `dim H¹ = dim H³` (Betti `b₁ = b₃`), which jointly make the pairing perfect.
This is exactly what Poincaré duality supplies at degrees `(1,3)`; a true theorem for closed
4-manifolds, carried here as the precise requirement while its geometric construction is the L2 core. -/
structure PoincareDual4Lo (X : TopCat) where
  /-- The fundamental-class functional `μ = ⟨·, [M]⟩ : H⁴(X;ℤ/2) → ℤ/2`. -/
  mu : Cohomology X 4 →ₗ[ZMod 2] ZMod 2
  /-- The `H¹×H³` cup pairing `cup13 : H¹ →ₗ H³ →ₗ H⁴`, `(a,b) ↦ a ∪ b`. -/
  cup13 : Cohomology X 1 →ₗ[ZMod 2] Cohomology X 3 →ₗ[ZMod 2] Cohomology X 4
  /-- The Bockstein `Sq¹ : H³ →ₗ H⁴` on `H³` (no top-square formula; abstract). -/
  sq1₃ : Cohomology X 3 →ₗ[ZMod 2] Cohomology X 4
  /-- `H¹(X;ℤ/2)` is finite-dimensional. -/
  findim₁ : FiniteDimensional (ZMod 2) (Cohomology X 1)
  /-- `H³(X;ℤ/2)` is finite-dimensional. -/
  findim₃ : FiniteDimensional (ZMod 2) (Cohomology X 3)
  /-- **Poincaré duality at `(1,3)`, non-degeneracy**: the cup pairing `a ↦ (b ↦ μ(a∪b))` from `H¹`
  to `(H³ →ₗ ZMod 2)` is injective. -/
  nondeg₁₃ : Function.Injective ⇑(cup13.compr₂ mu)
  /-- **Poincaré duality at `(1,3)`, dimension equality**: `dim H¹ = dim H³` (Betti `b₁ = b₃`). -/
  dimeq : Module.finrank (ZMod 2) (Cohomology X 1) = Module.finrank (ZMod 2) (Cohomology X 3)

variable (P₁₃ : PoincareDual4Lo X)

/-- The degree-`(1,3)` **cup pairing** `H¹ × H³ → ℤ/2`, `(a,b) ↦ μ(a ∪ b)`, of the `(1,3)` PD datum. -/
noncomputable def pairing13 : Cohomology X 1 →ₗ[ZMod 2] Cohomology X 3 →ₗ[ZMod 2] ZMod 2 :=
  P₁₃.cup13.compr₂ P₁₃.mu

/-- The **first Wu functional** `x ↦ ⟨Sq¹ x, [M]⟩ = μ(Sq¹ x)` — a `ZMod 2`-linear functional on `H³`.
The first Wu class `v₁` is its Poincaré-dual representative (in `H¹`). -/
noncomputable def wuFunctional1 : Cohomology X 3 →ₗ[ZMod 2] ZMod 2 :=
  P₁₃.mu.comp P₁₃.sq1₃

/-- The pairing map `H¹ → (H³ →ₗ ZMod 2)` is **bijective**: injective by Poincaré duality
(`P₁₃.nondeg₁₃`), hence surjective since `dim H¹ = dim H³ = dim (H³)*` (`P₁₃.dimeq` +
`Subspace.dual_finrank_eq`) and both are finite-dimensional. -/
theorem pairing13_bijective : Function.Bijective ⇑(pairing13 P₁₃) := by
  haveI := P₁₃.findim₁
  haveI := P₁₃.findim₃
  refine ⟨P₁₃.nondeg₁₃, ?_⟩
  have hdim : Module.finrank (ZMod 2) (Cohomology X 1) =
      Module.finrank (ZMod 2) (Cohomology X 3 →ₗ[ZMod 2] ZMod 2) := by
    rw [P₁₃.dimeq, Subspace.dual_finrank_eq]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp P₁₃.nondeg₁₃

/-- The **first Wu class `v₁ ∈ H¹(M;ℤ/2)`**: the Poincaré-dual representative of the first Wu
functional, i.e. the unique class with `⟨v₁ ∪ x, [M]⟩ = ⟨Sq¹ x, [M]⟩` for all `x ∈ H³`. Exists by
`pairing13_bijective`. -/
noncomputable def wuClass1 : Cohomology X 1 :=
  (Equiv.ofBijective _ (pairing13_bijective P₁₃)).symm (wuFunctional1 P₁₃)

/-- **The defining first-Wu relation** `⟨v₁ ∪ x, [M]⟩ = ⟨Sq¹ x, [M]⟩` for all `x ∈ H³`. This is the
genuine content of `v₁`: it represents the `Sq¹` functional under Poincaré duality, the input to
`v₁²` in the Wu formula `w₂ = v₂ + v₁²`. -/
theorem wu_relation_v1 (x : Cohomology X 3) :
    P₁₃.mu (P₁₃.cup13 (wuClass1 P₁₃) x) = P₁₃.mu (P₁₃.sq1₃ x) := by
  have h : pairing13 P₁₃ (wuClass1 P₁₃) = wuFunctional1 P₁₃ :=
    (Equiv.ofBijective _ (pairing13_bijective P₁₃)).apply_symm_apply (wuFunctional1 P₁₃)
  exact congrFun (congrArg DFunLike.coe h) x

/-! ### The Wu formula: `w₂ = v₂ + v₁²` -/

/-- The **singular Wu second class** `w₂ := v₂ + v₁² ∈ H²(M;ℤ/2)`, where `v₂ = wuClass2 P` (the middle
Wu class from `PoincareDualityWu`) and `v₁² = (wuClass1 P₁₃)∪(wuClass1 P₁₃) = cupSquareₗ (wuClass1 P₁₃)`.

DEFINED (not derived from an abstract tangent-bundle SW class): this is the Wu-theorem expression
`w = Sq(v)` specialized to a 4-manifold, `w₂ = v₂ + Sq¹ v₁ = v₂ + v₁²` (using `Sq¹ = (·)²` on `H¹`,
`sq1_eq_cupSquare_on_H1`). Documented as the manifold `w₂`; its load-bearing properties are PROVEN
below (`wuW2_eq`, `wuW2_eq_zero_iff`). -/
noncomputable def wuW2 (P : PoincareDual4Mid X) (P₁₃ : PoincareDual4Lo X) : Cohomology X 2 :=
  wuClass2 P + cupSquareₗ (wuClass1 P₁₃)

/-- `w₂` is the genuine sum `v₂ + v₁²` with `v₁² = v₁ ∪ v₁` — unfolding the definition to the explicit
Wu-formula shape. -/
theorem wuW2_eq (P : PoincareDual4Mid X) (P₁₃ : PoincareDual4Lo X) :
    wuW2 P P₁₃ = wuClass2 P + cupH (wuClass1 P₁₃) (wuClass1 P₁₃) := rfl

/-- **The Pin⁺ characterization** `w₂ = 0 ↔ v₂ = v₁²`: the singular Wu `w₂` vanishes exactly when the
middle Wu class equals the square of the first Wu class. This is the foundation-collapse criterion the
unoriented-bordism floor consumes (restricting the carrier to `w₂ = 0`). Non-vacuous: it is a genuine
equivalence between a vanishing in `H²` and an equation `v₂ = v₁ ∪ v₁` of two independently-defined
classes (`v₂` from the `(2,2)` PD datum, `v₁²` from the `(1,3)` datum). -/
theorem wuW2_eq_zero_iff (P : PoincareDual4Mid X) (P₁₃ : PoincareDual4Lo X) :
    wuW2 P P₁₃ = 0 ↔ wuClass2 P = cupH (wuClass1 P₁₃) (wuClass1 P₁₃) := by
  have hneg : ∀ y : Cohomology X 2, -y = y := fun y => by
    rw [neg_eq_iff_add_eq_zero, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  rw [wuW2, cupSquareₗ_apply, add_eq_zero_iff_eq_neg, hneg]

end SKEFTHawking.PoincareDualityWuFormula
