/-
# Phase 5q.H close-out (#196) — THE ⊗ℝ SCALAR-EXTENSION LAYER (the deferred wiring layer)

The `SingularRelativeCohomDeltaInt` / `SingularRelativeCapHadjInt` docstrings name a "separate ⊗ℝ wiring
layer" that carries the genuine integral pair-LES tower (`deltaRelHInt` δ, `capRelHInt` cap, the
`hadj_integral_core` PD-square) onto the `Fin n → ℝ` lattice substrate `NovikovRealPairLES` — the ℝ-linear
algebra engine whose fields are the ℝ-tensored images of those integral pieces. This module IS that layer's
FORM half: the base-change identification carrying the integral intersection form `interFormInt` to the
consumer's coordinate matrix `Bd.map (Int.cast : ℤ → ℝ)`.

## The route decision — BASIS-REPR-DIRECT (route (b)), NOT literal `TensorProduct ℝ`

`NovikovRealPairLES Bd` does NOT demand a literal `TensorProduct ℝ (Cohomology ∂W 2)`: its boundary space is
`Fin n → ℝ` and its boundary form is the *matrix* `Bd.map (Int.cast : ℤ → ℝ)` fed to `toQuadraticMap'` /
`polarBilin`. So the honest, low-friction identification is the **basis-repr-direct** route: a finite free
`ℤ`-basis `B : IntH2Basis ∂W` (the `#164`/`#190` disclosed datum — `⊗ℝ` kills the torsion, so the free
basis is a basis of `H²(∂W;ℝ)` too) sends a class `a` to its real coordinate vector
`fun i => (B.basis.repr a i : ℝ) : Fin n → ℝ`, and the Gram matrix of `interFormInt` on `B.basis` — literally
`interMatrix fc B` — is the matrix the substrate manipulates. No `TensorProduct` object, no `LinearMap.
baseChange` diamond: the coordinate `Fin n → ℝ` IS the `⊗ℝ`-image, addressed through `B.basis.repr` +
`Int.cast`. The single genuine content is the **base-changed Gram identity**
`(interFormInt fc a b : ℝ) = coord(a) ⬝ᵥ (interMatrix fc B).map cast *ᵥ coord(b)` (`interFormInt_eq_matrix_
dotProduct_repr` below), plus the polar-form factor (`polarBilin_map_cast_apply`).

Dimension discipline: `∂W` the 4-dim boundary; the forms on `H²`; the coordinate space `Fin n → ℝ`,
`n = b₂(∂W)`. `k₀`-free; rides the GENUINE `IntH2Basis` free-basis data (no synthetic grade).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.IntersectionMatrixInt

namespace SKEFTHawking.SingularRelativeRealBaseChange

open SKEFTHawking.SingularCohomologyInt
open scoped Matrix

/-! ## §1. The base-changed Gram identity for a ℤ-bilinear form on a finite free basis -/

variable {V : Type*} [AddCommGroup V] [Module ℤ V]

/-- **Bilinear expansion in a basis (over ℤ).** For a `ℤ`-bilinear form `f` and a finite basis `b`,
`f a c = ∑ i, ∑ j, (b.repr a i) * (b.repr c j) * f (b i) (b j)` — the Gram expansion. -/
theorem bilin_expand_basis {n : ℕ} (b : Module.Basis (Fin n) ℤ V)
    (f : V →ₗ[ℤ] V →ₗ[ℤ] ℤ) (a c : V) :
    f a c = ∑ i, ∑ j, b.repr a i * b.repr c j * f (b i) (b j) := by
  have hc : ∀ i : Fin n, f (b i) c = ∑ j, b.repr c j * f (b i) (b j) := by
    intro i
    conv_lhs => rw [← b.sum_repr c]
    rw [map_sum (f (b i))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [LinearMap.map_smul, smul_eq_mul]
  conv_lhs => rw [← b.sum_repr a]
  rw [map_sum f, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, hc i, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-! ## §2. The real coordinate vector and the base-changed Gram identity for `interFormInt` -/

variable {X : TopCat}

/-- **The real coordinate vector of an integral `H²` class** — `coord B a i = (B.basis.repr a i : ℝ)`,
the image of `a ∈ H²(∂W;ℤ)` in `H²(∂W;ℝ) = Fin n → ℝ` under the basis-repr-direct `⊗ℝ` identification. -/
noncomputable def coord (B : IntH2Basis X) (a : Cohomology X 2) : Fin B.rank → ℝ :=
  fun i => (B.basis.repr a i : ℝ)

@[simp] theorem coord_apply (B : IntH2Basis X) (a : Cohomology X 2) (i : Fin B.rank) :
    coord B a i = (B.basis.repr a i : ℝ) := rfl

/-- **The base-changed Gram identity (the FORM half of the ⊗ℝ layer).** The `ℝ`-cast intersection form
`⟨a ∪ b, [∂W]⟩` equals the coordinate bilinear value of the base-changed Gram matrix `interMatrix fc B`:
`(interFormInt fc a b : ℝ) = coord(a) ⬝ᵥ (interMatrix fc B).map cast *ᵥ coord(b)`. This is the honest
`H²(∂W;ℝ) ≅ Fin n → ℝ` identification carrying `interFormInt` to the consumer's `Bd.map Int.cast` — no
`TensorProduct` object, addressed through `B.basis.repr` + `Int.cast`. -/
theorem interFormInt_eq_matrix_dotProduct_repr (fc : IntFundamentalClass X) (B : IntH2Basis X)
    (a c : Cohomology X 2) :
    ((interFormInt fc a c : ℤ) : ℝ)
      = coord B a ⬝ᵥ (((interMatrix fc B).map (Int.cast : ℤ → ℝ)) *ᵥ coord B c) := by
  rw [bilin_expand_basis B.basis (interFormInt fc) a c]
  push_cast
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, interMatrix_apply, coord_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-! ## §3. The polar form of the boundary quadratic map, in coordinates -/

/-- **The polar form of `M.toQuadraticMap'`, in coordinates.** `polarBilin (M.toQuadraticMap') x y =
x ⬝ᵥ M *ᵥ y + y ⬝ᵥ M *ᵥ x` — the polarization of the matrix quadratic form is the (un-symmetrized) sum of
the two Gram values. For a symmetric `M` this is `2 · (x ⬝ᵥ M *ᵥ y)` (`polarBilin_toQuadraticMap'_isSymm`).
This is the boundary-form side of the substrate's `hadj`, in the coordinate language. -/
theorem polarBilin_toQuadraticMap'_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    QuadraticMap.polarBilin M.toQuadraticMap' x y = x ⬝ᵥ (M *ᵥ y) + y ⬝ᵥ (M *ᵥ x) := by
  -- `Matrix.toQuadraticMap'` is a deprecated *alias*: unfolding it lands on the real definition
  -- `Matrix.toQuadraticForm'`, which must also be in the set or every later lemma goes unused.
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, Matrix.toQuadraticMap',
    Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply',
    Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  ring

/-- **The polar form of a symmetric `M.toQuadraticMap'` is `2 ·` the Gram value.** For a symmetric matrix
`M`, `polarBilin (M.toQuadraticMap') x y = 2 · (x ⬝ᵥ M *ᵥ y)` (`y ⬝ᵥ M *ᵥ x = x ⬝ᵥ M *ᵥ y` by symmetry).
This is the factor-of-2 the substrate's `pairing` absorbs. -/
theorem polarBilin_toQuadraticMap'_isSymm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm)
    (x y : Fin n → ℝ) :
    QuadraticMap.polarBilin M.toQuadraticMap' x y = 2 * (x ⬝ᵥ (M *ᵥ y)) := by
  rw [polarBilin_toQuadraticMap'_apply]
  have hswap : y ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ (M *ᵥ y) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [show M j i = M i j from congrFun (congrFun hM i) j]
    ring
  rw [hswap]; ring

end SKEFTHawking.SingularRelativeRealBaseChange
