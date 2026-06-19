import Mathlib
import SKEFTHawking.SingularH0
import SKEFTHawking.SingularHomotopyInvariance

/-!
# `H₀(X; ℤ/2) ≅ ℤ/2` for a path-connected space — the augmentation iso

The augmentation `ε : C₀(X) → ℤ/2` (`SKEFTHawking.SingularH0.augmentation`) descends to
`ε̄ : H₀(X; ℤ/2) → ℤ/2` (`SKEFTHawking.SingularH0.augH`). On a **path-connected** space this descended
map is an isomorphism (reduced `H̃₀(X) = 0`): it is surjective always (a point's `0`-simplex hits `1`),
and the substantive injective half is the classic path-connectivity fill.

The fill is built from the **singular `1`-simplex of a path** `pathSimplex p`, the realization
`Δ¹ → X`, `t ↦ p(t 1)` (the second barycentric coordinate as the path parameter). Its two `0`-faces are
the constant simplices at the endpoints (`face_zero_pathSimplex`, `face_one_pathSimplex`), so
`∂(pathSimplex p) = [c_x] + [c_b]` (mod 2). Summing the chosen paths `b ⤳ (point of σ)` over a chain `z`
gives the **witness** `W z` with `∂(W z) = z + ε(z)·c_b` (`chainBoundary_pathWitness`); when `ε(z) = 0`
this exhibits `z` as a boundary, so `ε̄` is injective.

This is the degree-`0` base case of the sphere/local-homology induction `Hₙ(ℝⁿ, ℝⁿ∖0) ≅ ℤ/2`.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularH0
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularExcisionPushforward SKEFTHawking.SingularCohomologyMod2

namespace SKEFTHawking.SingularH0PathConnected

/-- The point of `Δ¹ = stdSimplex ℝ (Fin 2)` as a parameter in the unit interval: the second
barycentric coordinate `t 1 ∈ [0,1]`. -/
noncomputable def toUnitInterval (t : stdSimplex ℝ (Fin 2)) : unitInterval :=
  ⟨(t : Fin 2 → ℝ) 1, t.2.1 1, stdSimplex.le_one t 1⟩

/-- The barycentric-coordinate readout `Δ¹ → [0,1]` is continuous. -/
theorem continuous_toUnitInterval : Continuous toUnitInterval := by
  apply Continuous.subtype_mk
  exact (continuous_apply 1).comp continuous_subtype_val

/-- The continuous map `Δ¹ = stdSimplex ℝ (Fin 2) → X` underlying the singular 1-simplex of a path
`p : b ⤳ x`: read off the second barycentric coordinate `t 1 ∈ [0,1]` and apply the path. -/
noncomputable def pathSimplexMap {X : TopCat} {b x : ↑X} (p : Path b x) :
    C(stdSimplex ℝ (Fin 2), ↑X) :=
  ⟨fun t => p (toUnitInterval t), p.continuous.comp continuous_toUnitInterval⟩

/-- The **singular 1-simplex of a path** `p : b ⤳ x`: the realization `Δ¹ → X` of `pathSimplexMap`. -/
noncomputable def pathSimplex {X : TopCat} {b x : ↑X} (p : Path b x) :
    (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 1)) :=
  (X.toSSetObjEquiv (op (SimplexCategory.mk 1))).symm (pathSimplexMap p)

/-- **The `0`-th face of `pathSimplex p` is the constant simplex at the endpoint** `x`. The face `∂₀`
realizes precomposition with the coface `δ 0 : Δ⁰ → Δ¹` (the vertex `1`), at which the path-parameter
coordinate is `1`, so the realization is the constant map `p 1 = x`. -/
theorem face_zero_pathSimplex {X : TopCat} {b x : ↑X} (p : Path b x) :
    face (0 : Fin 2) (pathSimplex p) = constSimplex x 0 := by
  apply (X.toSSetObjEquiv (op (SimplexCategory.mk 0))).injective
  rw [pathSimplex, toSSetObjEquiv_symm_face, constSimplex, Equiv.apply_symm_apply]
  apply ContinuousMap.ext; intro t
  simp only [ContinuousMap.comp_apply, ContinuousMap.const_apply, pathSimplexMap,
    ContinuousMap.coe_mk]
  have key : toUnitInterval (stdSimplex.map (⇑(ConcreteCategory.hom (SimplexCategory.δ (0 : Fin 2)))) t)
      = 1 := by
    have ht : t = stdSimplex.vertex (0 : Fin 1) := Subsingleton.elim _ _
    rw [ht]
    erw [stdSimplex.map_vertex]
    rw [show (ConcreteCategory.hom (SimplexCategory.δ (0 : Fin 2))) (0 : Fin 1) = (1 : Fin 2) from by
      decide]
    apply Subtype.ext
    simp only [toUnitInterval, Set.Icc.coe_one, stdSimplex.vertex_coe, Pi.single_eq_same]
  rw [key]; exact p.target

/-- **The `1`-st face of `pathSimplex p` is the constant simplex at the start point** `b`. The face `∂₁`
realizes precomposition with the coface `δ 1 : Δ⁰ → Δ¹` (the vertex `0`), at which the path-parameter
coordinate is `0`, so the realization is the constant map `p 0 = b`. -/
theorem face_one_pathSimplex {X : TopCat} {b x : ↑X} (p : Path b x) :
    face (1 : Fin 2) (pathSimplex p) = constSimplex b 0 := by
  apply (X.toSSetObjEquiv (op (SimplexCategory.mk 0))).injective
  rw [pathSimplex, toSSetObjEquiv_symm_face, constSimplex, Equiv.apply_symm_apply]
  apply ContinuousMap.ext; intro t
  simp only [ContinuousMap.comp_apply, ContinuousMap.const_apply, pathSimplexMap,
    ContinuousMap.coe_mk]
  have key : toUnitInterval (stdSimplex.map (⇑(ConcreteCategory.hom (SimplexCategory.δ (1 : Fin 2)))) t)
      = 0 := by
    have ht : t = stdSimplex.vertex (0 : Fin 1) := Subsingleton.elim _ _
    rw [ht]
    erw [stdSimplex.map_vertex]
    rw [show (ConcreteCategory.hom (SimplexCategory.δ (1 : Fin 2))) (0 : Fin 1) = (0 : Fin 2) from by
      decide]
    apply Subtype.ext
    simp only [toUnitInterval, Set.Icc.coe_zero, stdSimplex.vertex_coe, Pi.single_eq_of_ne,
      Ne, one_ne_zero, not_false_eq_true]
  rw [key]; exact p.source

/-- **The boundary of the path 1-simplex**: `∂(pathSimplex p) = [c_x] + [c_b]` (mod 2), i.e. its two
`0`-faces are the constant simplices at the endpoint `x` and the start `b`. This is the chain whose
boundary realizes "a path connects `b` to `x`", the engine of the injectivity half. -/
theorem chainBoundary_pathSimplex {X : TopCat} {b x : ↑X} (p : Path b x) :
    chainBoundary X 0 (Finsupp.single (pathSimplex p) 1)
      = Finsupp.single (constSimplex x 0) 1 + Finsupp.single (constSimplex b 0) 1 := by
  rw [chainBoundary_single, boundaryBasis, Fin.sum_univ_two, face_zero_pathSimplex,
    face_one_pathSimplex]

/-! ## §2. Every `0`-simplex is a constant simplex -/

/-- The **point of a singular `0`-simplex** `σ`: the image in `X` of the unique point of `Δ⁰`. -/
noncomputable def simplexPoint {X : TopCat} (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 0))) :
    ↑X :=
  (X.toSSetObjEquiv (op (SimplexCategory.mk 0)) σ) default

/-- **Every singular `0`-simplex is the constant simplex at its point** (`Δ⁰` is a one-point space, so a
map `Δ⁰ → X` is determined by, and is constant at, its single value). -/
theorem eq_constSimplex {X : TopCat}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 0))) :
    σ = constSimplex (simplexPoint σ) 0 := by
  apply (X.toSSetObjEquiv (op (SimplexCategory.mk 0))).injective
  rw [constSimplex, Equiv.apply_symm_apply]
  apply ContinuousMap.ext; intro t
  rw [ContinuousMap.const_apply, simplexPoint, Subsingleton.elim t default]

/-! ## §3. The path-filling witness and the boundary identity -/

variable {X : TopCat} [PathConnectedSpace ↑X]

/-- The **path-filling witness** of a `0`-chain, relative to a basepoint `b`: the `ℤ/2`-linear map
sending a `0`-simplex `σ` to the `1`-simplex of a chosen path `b ⤳ (point of σ)`. Its boundary fills
`σ` against the constant chain at `b` (`chainBoundary_pathWitness`). -/
noncomputable def pathWitness (b : ↑X) : SingularChain X 0 →ₗ[ZMod 2] SingularChain X 1 :=
  Finsupp.linearCombination (ZMod 2)
    (fun σ => Finsupp.single (pathSimplex (PathConnectedSpace.somePath b (simplexPoint σ))) 1)

/-- The path-filling witness on a basis `0`-simplex `σ` is the `1`-simplex of the chosen path. -/
theorem pathWitness_single (b : ↑X)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 0))) :
    pathWitness b (Finsupp.single σ 1)
      = Finsupp.single (pathSimplex (PathConnectedSpace.somePath b (simplexPoint σ))) 1 := by
  rw [pathWitness, Finsupp.linearCombination_single, one_smul]

/-- **The witness fills a basis `0`-simplex against the constant chain at `b`**:
`∂(W (single σ 1)) = single σ 1 + single c_b 1`. The chosen path's `1`-simplex has its two endpoints
`σ` (the point of `σ`, since every `0`-simplex is constant — `eq_constSimplex`) and `c_b`. -/
theorem chainBoundary_pathWitness_single (b : ↑X)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 0))) :
    chainBoundary X 0 (pathWitness b (Finsupp.single σ 1))
      = Finsupp.single σ 1 + Finsupp.single (constSimplex b 0) 1 := by
  rw [pathWitness_single, chainBoundary_pathSimplex, ← eq_constSimplex]

/-- **The boundary of the witness fills `z` against `ε(z)·c_b`**: `∂(W z) = z + ε(z)·c_b` for every
`0`-chain `z`. Linear in `z`, checked on the basis via `chainBoundary_pathWitness_single` (the
constant-`c_b` tail accumulates `ε(z) = ∑ z_σ` copies). -/
theorem chainBoundary_pathWitness (b : ↑X) (z : SingularChain X 0) :
    chainBoundary X 0 (pathWitness b z)
      = z + augmentation X z • Finsupp.single (constSimplex b 0) 1 := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, map_add, h₁, h₂, map_add, add_smul]
      abel
  | single σ a =>
      rw [show Finsupp.single σ a = a • Finsupp.single σ (1 : ZMod 2) by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one], map_smul, map_smul,
        chainBoundary_pathWitness_single, map_smul, augmentation_single, smul_add, smul_eq_mul,
        mul_one]

/-! ## §4. The injectivity of `ε̄` and the iso `H₀ ≅ ℤ/2` -/

/-- **A `0`-chain with vanishing augmentation is a boundary** (the substantive half): if `ε(z) = 0`
then `z = ∂(W z)` (the constant-`c_b` tail vanishes), so `z ∈ im ∂₁`. The classic path-connectivity
fill: a chosen path joins each simplex's point to the basepoint `b`. -/
theorem mem_boundaries_of_augmentation_eq_zero (b : ↑X) (z : SingularChain X 0)
    (hz : augmentation X z = 0) : z ∈ boundaries X 0 := by
  refine ⟨pathWitness b z, ?_⟩
  rw [chainBoundary_pathWitness, hz, zero_smul, add_zero]

/-- **The augmentation `ε̄ : H₀(X; ℤ/2) → ℤ/2` is injective** for path-connected `X` (reduced
`H̃₀(X) = 0`): a class with `ε̄ = 0` is represented by a `0`-chain of vanishing augmentation, which is a
boundary by `mem_boundaries_of_augmentation_eq_zero`, hence the class is `0`. -/
theorem augH_injective : Function.Injective (augH X) := by
  let b : ↑X := Classical.arbitrary ↑X
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro y hy
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [LinearMap.mem_ker] at hy
  have hz : augmentation X (z : SingularChain X 0) = 0 := hy
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.mem_comap.mpr (mem_boundaries_of_augmentation_eq_zero b (z : SingularChain X 0) hz))

/-- **`H₀(X; ℤ/2) ≅ ℤ/2` for a path-connected space** `X`: the augmentation `ε̄ : H₀(X; ℤ/2) → ℤ/2`,
which is always surjective on a nonempty space and injective exactly when `X` is reduced-acyclic, is a
`ℤ/2`-linear isomorphism. The degree-`0` base case of the sphere/local-homology computation. -/
noncomputable def homologyZeroPathConnectedEquiv : Homology X 0 ≃ₗ[ZMod 2] ZMod 2 :=
  LinearEquiv.ofBijective (augH X)
    ⟨augH_injective, augH_surjective X (constSimplex (Classical.arbitrary ↑X) 0)⟩

end SKEFTHawking.SingularH0PathConnected
