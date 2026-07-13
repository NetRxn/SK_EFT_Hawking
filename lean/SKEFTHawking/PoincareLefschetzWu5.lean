/-
# Phase 5q.H (W-A NEW-BUILD item 1) — the Poincaré–Lefschetz Wu tower for compact manifolds-with-boundary

**The route-independent critical-path tower.** Any honest structured-bordism relation whose faithful
carrier's `Bor` conditions constrain the tangential structure of a bordism `W` needs the Wu classes
`w₁(W)`, `w₂(W)` of the compact `(n+1)`-manifold-with-boundary `W` (`BordismGroup.lean`: `W` charted
on `H'`, `IsManifold J k`, `CompactSpace`, `T2` via the refined relation `IsT2DataBordant`). For the
5q.H bordism `W` (`n+1 = 5`) the odd/`ℤ/16` content is carried by the `w₁`-dual 3-manifold `V` and the
`w₂`-dual characteristic surface `Q`; both are pinned by Poincaré–**Lefschetz** duality of the pair
`(W, ∂W)`. This module opens that tower.

## The boundary-as-`Set` constraint (design-forcing)

`Mathlib.ModelWithCorners.boundary J W` is only a **`Set W`** — the boundary-as-manifold is NOT
available (`InteriorBoundary.lean` lists "boundary is a submanifold" as an unproven goal). So every
statement here uses the boundary purely as a subspace: the in-tree relative machinery
`SingularRelativeHomologyMod2.RelativeHomology (S : Set X)` /
`SingularRelativeCohomologyMod2.RelativeCohomology (S : Set X)` is defined for an **arbitrary** subspace
`S ⊆ X` (relative chains = the quotient `C_•(X)/C_•(S)`; relative cochains = the annihilator of the
subspace chains), so it applies verbatim to `S := J.boundary W : Set W` with `X := TopCat.of W`. No
boundary-manifold datum is ever formed, so the membrane-level non-Hausdorff collapse
(`SETTLED_FORKS.md: membrane-level-nonhausdorff-collapse`) has no surface to attack: this module is
entirely at cohomology-of-a-pair level and never introduces a manifold-typed field.

## The datum pattern (the 5q.G bundle-the-duality-data design, matching `PoincareDual4Mid`/`Lo`)

Mathlib has neither the fundamental class nor Poincaré/Lefschetz duality for manifolds. The **closed**
4-manifold Wu tower (`PoincareDualityWu` / `PoincareDualityWuFormula`) handled this by bundling the
precise duality manifestation the Wu class consumes as a **structure argument** (`PoincareDual4Mid`,
`PoincareDual4Lo`) and proving the Wu class as its genuine consequence; the geometric construction of
that datum from the manifold was discharged later (`SingularPD4Instances`, phase G1/X6). We follow the
identical pattern for the pair `(W, ∂W)`:

`LefschetzWuDatum X S k nk n` bundles, at a degree pair `(k, nk)` with `k + nk = n` (Lefschetz-dual
degrees for the pair `(W, ∂W)` of an `n`-manifold-with-boundary — here `n = 5`):
* `mu  : H^n(W,∂W;ℤ/2) → ℤ/2` — the **relative fundamental-class functional** `⟨·, [W,∂W]⟩`, where
  `[W,∂W] ∈ H_n(W,∂W;ℤ/2)` is the (mod-2) relative fundamental class of the compact manifold-with-
  boundary;
* `cup : H^k(W) ×  H^{nk}(W,∂W) → H^n(W,∂W)` — the **relative cup product** (absolute cohomology cupped
  into relative cohomology → relative). Carried abstractly (the project's singular cup is built only at
  `(1,1)`/`(2,2)` absolute; the absolute×relative→relative cup is the next foundation brick), exactly as
  `PoincareDual4Lo.cup13` carries the `H¹×H³→H⁴` cup abstractly;
* `sqOp : H^{nk}(W,∂W) → H^n(W,∂W)` — the Steenrod square `Sq^k` on relative cohomology (`Sq¹` at
  `nk=4`, `Sq²` at `nk=3`; carried abstractly, as `PoincareDual4Lo.sq1₃` carries the Bockstein);
* `findimAbs`, `findimRel`, `nondeg`, `dimeq` — finite-dimensionality of both sides, the **Lefschetz
  non-degeneracy** (`a ↦ (b ↦ μ(a∪b))` injective `H^k(W) → (H^{nk}(W,∂W))*`), and the Lefschetz Betti
  equality `dim H^k(W) = dim H^{nk}(W,∂W)`. Jointly: the Lefschetz pairing is perfect.

From these, `wuClass P : H^k(W)` is the Lefschetz-dual representative of the Wu functional
`x ↦ μ(Sq^k x)`, characterised by `wu_relation : μ(v_k ∪ x) = μ(Sq^k x)` for all `x ∈ H^{nk}(W,∂W)`.
This is degree-agnostic: it is the honest general Poincaré–Lefschetz Wu-class construction for a
compact manifold-with-boundary at any dimension, specialised below to `n = 5`.

## The `n = 5` Wu classes and the Wu formula (`W-A` consumables)

Instantiating the generic construction at the two Lefschetz-dual degree pairs of a compact
5-manifold-with-boundary:
* `wuClassW1 : H^1(W)` from the `(1,4)` datum (`v₁`),
* `wuClassW2 : H^2(W)` from the `(2,3)` datum (`v₂`),

the Wu theorem `w = Sq(v)` gives, in `H^•(W;ℤ/2)`, `w₁(W) = v₁` (`wuW1`) and
`w₂(W) = v₂ + Sq¹v₁ = v₂ + v₁²` (`wuW2`, using `Sq¹ = (·)²` on `H¹` via
`PoincareDualityWuFormula.cupSquareₗ`). Its load-bearing property is the Pin⁺-type characterisation
`w₂(W) = 0 ↔ v₂ = v₁²` (`wuW2_eq_zero_iff`) — the shape the carrier's `Bor` conditions consume.

## Dependency order / recursion flag (design item 2c)

`wuClassW2` (`v₂`) is Lefschetz-dual to the **characteristic surface** `Q ⊆ W` (`[Q] ∈ H₂(W,∂W)` dual to
`w₂(W)`); the odd bit rides on `V ⊆ W` dual to `w₁(W)` (`[V] ∈ H₃(W,∂W)`). `Q`'s own quadratic-
enhancement theory (Guillou–Marin / Brown) is a **lower-dimensional** tower — a surface (with boundary
on `∂W`), whose own duality is 2-dimensional and does NOT recurse back into this 5-dimensional tower.
The recursion terminates: the 5-tower supplies the dual classes `[Q]`, `[V]`; their intrinsic
enhancement theory is the in-tree Brown/ABK algebra (`Z4Quadratic`, `brown`), consumed downstream, not
re-derived here. This module produces only the cohomology-level `w₁(W)`, `w₂(W)` and the duality
non-degeneracy that names `[Q]`, `[V]`; it does not construct `Q`, `V`, or their enhancements.

All cohomology is the project's genuine singular ℤ/2 (co)homology (`SingularCohomologyMod2`,
`SingularRelativeCohomologyMod2`). Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`,
no new project axiom, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularCohomologyMod2
import SKEFTHawking.SingularRelativeCohomologyMod2
import SKEFTHawking.PoincareDualityWuFormula

namespace SKEFTHawking.PoincareLefschetzWu5

open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.PoincareDualityWuFormula

variable {X : TopCat} {S : Set X}

/-! ## §1. The generic Poincaré–Lefschetz Wu datum and its perfect pairing -/

/-- A **mod-2 Poincaré–Lefschetz duality datum** for a compact `n`-manifold-with-boundary `(W, ∂W)` at
the Lefschetz-dual degree pair `(k, nk)` (`k + nk = n`), `X := TopCat.of W`, `S := ∂W`. It bundles the
exact manifestation of Lefschetz duality that the Wu class `v_k ∈ H^k(W)` consumes:
* `mu`   — the relative fundamental-class functional `⟨·, [W,∂W]⟩ : H^n(W,∂W;ℤ/2) → ℤ/2`,
* `cup`  — the relative cup product `H^k(W) × H^{nk}(W,∂W) → H^n(W,∂W)` (carried abstractly),
* `sqOp` — the Steenrod square `Sq^k : H^{nk}(W,∂W) → H^n(W,∂W)` (carried abstractly),
* `findimAbs`/`findimRel` — finite-dimensionality of `H^k(W)` and `H^{nk}(W,∂W)`,
* `nondeg` — Lefschetz non-degeneracy: `a ↦ (b ↦ μ(cup a b))` is injective `H^k(W) → (H^{nk}(W,∂W))*`,
* `dimeq` — the Lefschetz Betti equality `dim H^k(W) = dim H^{nk}(W,∂W)`.
`nondeg` + `dimeq` + finite-dimensionality make the pairing **perfect** (`pairing_bijective`). Mirrors
`PoincareDualityWuFormula.PoincareDual4Lo` with the second cup argument in RELATIVE cohomology. -/
structure LefschetzWuDatum (X : TopCat) (S : Set X) (k nk n : ℕ) where
  /-- The relative fundamental-class functional `μ = ⟨·, [W,∂W]⟩ : H^n(W,∂W;ℤ/2) → ℤ/2`. -/
  mu : RelativeCohomology S n →ₗ[ZMod 2] ZMod 2
  /-- The relative cup product `H^k(W) × H^{nk}(W,∂W) → H^n(W,∂W)`, `(a,b) ↦ a ∪ b`. -/
  cup : Cohomology X k →ₗ[ZMod 2] RelativeCohomology S nk →ₗ[ZMod 2] RelativeCohomology S n
  /-- The Steenrod square `Sq^k : H^{nk}(W,∂W) → H^n(W,∂W)` on relative cohomology. -/
  sqOp : RelativeCohomology S nk →ₗ[ZMod 2] RelativeCohomology S n
  /-- `H^k(W;ℤ/2)` is finite-dimensional. -/
  findimAbs : FiniteDimensional (ZMod 2) (Cohomology X k)
  /-- `H^{nk}(W,∂W;ℤ/2)` is finite-dimensional. -/
  findimRel : FiniteDimensional (ZMod 2) (RelativeCohomology S nk)
  /-- **Lefschetz non-degeneracy**: `a ↦ (b ↦ μ(a∪b))` is injective `H^k(W) → (H^{nk}(W,∂W))*`. -/
  nondeg : Function.Injective ⇑(cup.compr₂ mu)
  /-- **Lefschetz Betti equality**: `dim H^k(W) = dim H^{nk}(W,∂W)`. -/
  dimeq : Module.finrank (ZMod 2) (Cohomology X k)
        = Module.finrank (ZMod 2) (RelativeCohomology S nk)

variable {k nk n : ℕ}

/-- The **Lefschetz pairing** `H^k(W) × H^{nk}(W,∂W) → ℤ/2`, `(a,b) ↦ μ(a∪b)`, of the datum. -/
noncomputable def pairing (P : LefschetzWuDatum X S k nk n) :
    Cohomology X k →ₗ[ZMod 2] RelativeCohomology S nk →ₗ[ZMod 2] ZMod 2 :=
  P.cup.compr₂ P.mu

/-- The Lefschetz pairing map `H^k(W) → (H^{nk}(W,∂W))*` is **bijective**: injective by Lefschetz
non-degeneracy (`P.nondeg`), hence surjective since `dim H^k(W) = dim H^{nk}(W,∂W) = dim (H^{nk}(W,∂W))*`
(`P.dimeq` + `Subspace.dual_finrank_eq`) with both sides finite-dimensional. The pairing is perfect. -/
theorem pairing_bijective (P : LefschetzWuDatum X S k nk n) : Function.Bijective ⇑(pairing P) := by
  haveI := P.findimAbs
  haveI := P.findimRel
  refine ⟨P.nondeg, ?_⟩
  have hdim : Module.finrank (ZMod 2) (Cohomology X k) =
      Module.finrank (ZMod 2) (RelativeCohomology S nk →ₗ[ZMod 2] ZMod 2) := by
    rw [P.dimeq, Subspace.dual_finrank_eq]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp P.nondeg

/-! ## §2. The Wu class and the defining Wu relation (degree-agnostic) -/

/-- The **Wu functional** `x ↦ ⟨Sq^k x, [W,∂W]⟩ = μ(Sq^k x)` on `H^{nk}(W,∂W)` — a `ZMod 2`-linear
functional. The Wu class `v_k` is its Lefschetz-dual representative. -/
noncomputable def wuFunctional (P : LefschetzWuDatum X S k nk n) :
    RelativeCohomology S nk →ₗ[ZMod 2] ZMod 2 :=
  P.mu.comp P.sqOp

/-- The **Wu class `v_k ∈ H^k(W;ℤ/2)`**: the Lefschetz-dual representative of the Wu functional, i.e.
the unique class with `⟨v_k ∪ x, [W,∂W]⟩ = ⟨Sq^k x, [W,∂W]⟩` for all `x ∈ H^{nk}(W,∂W)`. Exists and is
unique by `pairing_bijective`. -/
noncomputable def wuClass (P : LefschetzWuDatum X S k nk n) : Cohomology X k :=
  (Equiv.ofBijective _ (pairing_bijective P)).symm (wuFunctional P)

/-- **The defining Wu relation** `⟨v_k ∪ x, [W,∂W]⟩ = ⟨Sq^k x, [W,∂W]⟩` for all `x ∈ H^{nk}(W,∂W)`.
This is the genuine content of `v_k`: it represents the `Sq^k` functional under Poincaré–Lefschetz
duality of the pair `(W, ∂W)`. -/
theorem wu_relation (P : LefschetzWuDatum X S k nk n) (x : RelativeCohomology S nk) :
    P.mu (P.cup (wuClass P) x) = P.mu (P.sqOp x) := by
  have h : pairing P (wuClass P) = wuFunctional P :=
    (Equiv.ofBijective _ (pairing_bijective P)).apply_symm_apply (wuFunctional P)
  exact congrFun (congrArg DFunLike.coe h) x

/-! ## §3. The `n = 5` Wu classes `w₁(W)`, `w₂(W)` and the Wu formula `w₂ = v₂ + v₁²`

For a compact 5-manifold-with-boundary `W`, the Lefschetz-dual degree pairs are `(1,4)` (→ `v₁`) and
`(2,3)` (→ `v₂`). `w₁(W) = v₁` and `w₂(W) = v₂ + Sq¹v₁ = v₂ + v₁²` (Wu theorem `w = Sq(v)`, with
`Sq¹ = (·)²` on `H¹`). The two data share the same `μ` at the instantiation but are taken as separate
arguments (matching `PoincareDualityWuFormula.wuW2` taking `PoincareDual4Mid` + `PoincareDual4Lo`). -/

variable (P₁₄ : LefschetzWuDatum X S 1 4 5) (P₂₃ : LefschetzWuDatum X S 2 3 5)

/-- The **first Wu class** `v₁ ∈ H^1(W;ℤ/2)` of the compact 5-manifold-with-boundary, from the `(1,4)`
Lefschetz datum. -/
noncomputable def wuClassW1 : Cohomology X 1 := wuClass P₁₄

/-- The **middle Wu class** `v₂ ∈ H^2(W;ℤ/2)` of the compact 5-manifold-with-boundary, from the `(2,3)`
Lefschetz datum. -/
noncomputable def wuClassW2 : Cohomology X 2 := wuClass P₂₃

/-- **The first Stiefel–Whitney class** `w₁(W) = v₁`: on any manifold the first Wu class equals the
first SW class (`w₁ = v₁`, the degree-1 Wu formula `w = Sq(v)` with only `Sq⁰v₁ = v₁`). -/
noncomputable def wuW1 : Cohomology X 1 := wuClassW1 P₁₄

@[simp] theorem wuW1_eq : wuW1 P₁₄ = wuClass P₁₄ := rfl

/-- **The second Stiefel–Whitney class** `w₂(W) = v₂ + v₁²` of the compact 5-manifold-with-boundary
(Wu theorem `w = Sq(v)`: `w₂ = v₂ + Sq¹v₁ = v₂ + v₁²`, using `Sq¹ = (·)²` on `H¹`). DEFINED as
`v₂ + v₁²` (not derived from an abstract tangent-bundle SW class — the manifold tangent bundle and its
SW classes are not in Mathlib for singular manifolds); its load-bearing properties are PROVEN below. -/
noncomputable def wuW2 : Cohomology X 2 := wuClassW2 P₂₃ + cupSquareₗ (wuClassW1 P₁₄)

/-- `w₂(W)` is the genuine sum `v₂ + v₁²` with `v₁² = v₁ ∪ v₁`. -/
theorem wuW2_eq : wuW2 P₁₄ P₂₃ = wuClassW2 P₂₃ + cupH (wuClassW1 P₁₄) (wuClassW1 P₁₄) := rfl

/-- **The Pin⁺-type characterisation** `w₂(W) = 0 ↔ v₂ = v₁²`: the singular Wu `w₂(W)` vanishes exactly
when the middle Wu class equals the square of the first Wu class. This is the shape the faithful
carrier's `Bor` conditions consume (restricting to `w₂ = 0`). Non-vacuous: a genuine equivalence
between a vanishing in `H²(W)` and an equation `v₂ = v₁ ∪ v₁` of two independently-defined Lefschetz-
dual classes (`v₂` from the `(2,3)` datum, `v₁²` from the `(1,4)` datum). -/
theorem wuW2_eq_zero_iff :
    wuW2 P₁₄ P₂₃ = 0 ↔ wuClassW2 P₂₃ = cupH (wuClassW1 P₁₄) (wuClassW1 P₁₄) := by
  have hneg : ∀ y : Cohomology X 2, -y = y := fun y => by
    rw [neg_eq_iff_add_eq_zero, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  rw [wuW2, cupSquareₗ_apply, add_eq_zero_iff_eq_neg, hneg]

end SKEFTHawking.PoincareLefschetzWu5
