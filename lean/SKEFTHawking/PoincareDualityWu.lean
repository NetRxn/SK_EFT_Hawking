/-
# Phase 5q.F (fully-unconditional strengthening, w₂-foundation brick 5) — the Wu class `v₂` from Poincaré duality

Toward the **fully-unconditional** `Ω₄^{Pin⁺} ≅ ℤ/16` on the full bordism-group carrier (collapsing the
unoriented-bordism "floor"): the floor is collapsed by restricting the carrier to genuine Pin⁺ classes, which
needs `w₂(TM) ∈ H²(M;ℤ/2)` as a manifold invariant. The route to `w₂` is the **Wu formula** `w = Sq(v)`,
whose input is the **Wu class** `v_k`, defined by Poincaré duality:

  `⟨v_k ∪ x, [M]⟩ = ⟨Sq^k x, [M]⟩`   for all `x ∈ H^{n-k}(M;ℤ/2)`.

This module builds `v₂` for a closed 4-manifold at the middle dimension (`k = 2`, `n = 4`): the element of
`H²(M;ℤ/2)` representing the functional `x ↦ ⟨Sq²x, [M]⟩ = ⟨x∪x, [M]⟩` under the middle cup pairing. It
builds on this phase's genuine singular ℤ/2 cohomology (`SingularCohomologyMod2`: `cupH24 : H²×H²→H⁴`,
`cupSquare2`/`cupSquare2_add` = the top `Sq²` on `H²`) + homology/Kronecker (`SingularHomologyMod2`).

## Scope (honest, NOT a hypothesis-relocation)
The **Poincaré-duality datum** (`PoincareDual4Mid`) — a fundamental-class functional `μ : H⁴→ℤ/2` plus the
NON-DEGENERACY of the middle cup pairing, with `H²` finite-dimensional — is the precise manifestation of
Poincaré duality the Wu class consumes. It is a **true theorem** for every closed 4-manifold (every manifold
is ℤ/2-orientable), but Mathlib has neither the fundamental class nor Poincaré duality for manifolds
(verified 2026-06-15 via semantic search). So the *construction* of `μ` + `nondeg` from the manifold is the
remaining foundation (the next bricks: the ℤ/2 fundamental class of a closed manifold + the PD pairing); this
module builds the Wu class as its genuine consequence, making that PD-requirement exact. Kernel-pure.
-/
import Mathlib
import SKEFTHawking.SingularCohomologyMod2
import SKEFTHawking.SingularHomologyMod2

namespace SKEFTHawking.PoincareDualityWu

open SKEFTHawking.SingularCohomologyMod2

variable {X : TopCat}

/-- The cup square as a **ℤ/2-linear** functional ingredient: over `ZMod 2` the additive top-square
`cupSquare2 : H² → H⁴` (`cupSquare2_add`) is automatically `ZMod 2`-linear (the only scalars are `0, 1`). -/
noncomputable def cupSquare2ₗ : Cohomology X 2 →ₗ[ZMod 2] Cohomology X 4 where
  toFun := cupSquare2
  map_add' := cupSquare2_add
  map_smul' c x := by
    show cupSquare2 (c • x) = c • cupSquare2 x
    rw [cupSquare2_apply, cupSquare2_apply, map_smul, map_smul, LinearMap.smul_apply, smul_smul,
      (by decide : ∀ d : ZMod 2, d * d = d) c]

/-- A **mod-2 Poincaré-duality datum for a closed 4-manifold at the middle dimension**: a fundamental-class
functional `μ : H⁴(X;ℤ/2) → ℤ/2` (`= ⟨·,[M]⟩`), finite-dimensionality of `H²`, and the NON-DEGENERACY of the
cup pairing `(a,b) ↦ μ(a ∪ b)` on `H²` — i.e. the map `a ↦ (b ↦ μ(cupH24 a b))` from `H²` to its dual is
injective. This is exactly what Poincaré duality supplies at the middle dimension; a true theorem for closed
4-manifolds, carried here as the precise requirement while its geometric construction (the fundamental class
+ PD) is the next foundation brick. -/
structure PoincareDual4Mid (X : TopCat) where
  /-- The fundamental-class functional `μ = ⟨·, [M]⟩ : H⁴(X;ℤ/2) → ℤ/2`. -/
  mu : Cohomology X 4 →ₗ[ZMod 2] ZMod 2
  /-- `H²(X;ℤ/2)` is finite-dimensional (finitely-generated homology of a closed manifold). -/
  findim : FiniteDimensional (ZMod 2) (Cohomology X 2)
  /-- **Poincaré duality at the middle dimension**: the cup pairing `(a,b) ↦ μ(a∪b)` on `H²` is
  non-degenerate — the induced map `H² → (H² →ₗ ZMod 2)` is injective. -/
  nondeg : Function.Injective ⇑((cupH24 (X := X)).compr₂ mu)

variable (P : PoincareDual4Mid X)

/-- The middle **cup pairing** `H² × H² → ℤ/2`, `(a,b) ↦ μ(a∪b)`, of the PD datum — symmetric (from
`cupH24_symm`) and non-degenerate (`P.nondeg`). -/
noncomputable def pairing : Cohomology X 2 →ₗ[ZMod 2] Cohomology X 2 →ₗ[ZMod 2] ZMod 2 :=
  (cupH24 (X := X)).compr₂ P.mu

/-- The **Wu functional** `x ↦ ⟨Sq²x, [M]⟩ = μ(x∪x)` — a genuine `ZMod 2`-linear functional on `H²`
(`Sq² = cupSquare2ₗ` is linear over ℤ/2). The Wu class `v₂` is its Poincaré-dual representative. -/
noncomputable def wuFunctional : Cohomology X 2 →ₗ[ZMod 2] ZMod 2 :=
  P.mu.comp cupSquare2ₗ

/-- The pairing map `H² → (H² →ₗ ZMod 2)` is **bijective**: injective by Poincaré duality (`P.nondeg`),
hence surjective since `H²` is finite-dimensional and `H²` and its dual have equal dimension. -/
theorem pairing_bijective : Function.Bijective ⇑(pairing P) := by
  haveI := P.findim
  exact ⟨P.nondeg, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq (K := ZMod 2) (V := Cohomology X 2)).symm).mp P.nondeg⟩

/-- The **Wu class `v₂ ∈ H²(M;ℤ/2)`**: the Poincaré-dual representative of the Wu functional, i.e. the unique
class with `⟨v₂ ∪ x, [M]⟩ = ⟨Sq²x, [M]⟩` for all `x`. Exists by `pairing_bijective`. -/
noncomputable def wuClass2 : Cohomology X 2 :=
  (Equiv.ofBijective _ (pairing_bijective P)).symm (wuFunctional P)

/-- **The defining Wu relation** `⟨v₂ ∪ x, [M]⟩ = ⟨Sq²x, [M]⟩` for all `x ∈ H²` (`Sq²x = x∪x`). This is the
genuine content: `v₂` represents the top-square functional under Poincaré duality, the input to the Wu
formula `w₂ = v₂ + v₁²` (next brick). -/
theorem wu_relation (x : Cohomology X 2) :
    P.mu (cupH24 (wuClass2 P) x) = P.mu (cupSquare2 x) := by
  have h : pairing P (wuClass2 P) = wuFunctional P :=
    (Equiv.ofBijective _ (pairing_bijective P)).apply_symm_apply (wuFunctional P)
  exact congrFun (congrArg DFunLike.coe h) x

end SKEFTHawking.PoincareDualityWu
