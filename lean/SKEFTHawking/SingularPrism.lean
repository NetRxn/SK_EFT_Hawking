import Mathlib
import SKEFTHawking.SingularExcisionPushforward

/-!
# The prism operator and homotopy invariance of singular ℤ/2 homology

Given a homotopy `H : X × I → Y` between `f, g : X → Y`, the prism operator `P : Cₙ(X) → Cₙ₊₁(Y)`
is a chain homotopy witnessing `f_# ≃ g_#`, hence homotopic maps induce equal maps on singular
homology. The construction triangulates each prism `Δⁿ × I` into `n + 1` affine `(n+1)`-simplices

  `a_i : Δⁿ⁺¹ → Δⁿ × I`,  `ê_k ↦ (e_k, 0)` for `k ≤ i`, `(e_{k-1}, 1)` for `k > i`,

and post-composes `H ∘ (σ × id) ∘ a_i`. Because the `a_i` are **affine** (vertices map to vertices),
there is no continuity seam — the cone/division formula is avoided entirely.

This is the foundation for `Hₖ(ℝⁿ) = 0` (acyclicity of star-convex sets via the contraction
homotopy) and the homotopy equivalences `ℝⁿ ∖ 0 ≃ Sⁿ⁻¹` used in the local-homology computation.

## §1. The affine prism maps

`prismAlpha i : Δⁿ⁺¹ → Δⁿ` is the simplicial degeneracy `Fin.predAbove i` realized affinely (the
`Δⁿ`-component of `a_i`); `prismBeta i : Δⁿ⁺¹ → I` is the `[0,1]`-component (sum of the coordinates
strictly above `i`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularExcisionPushforward

namespace SKEFTHawking.SingularPrism

/-- The `Δⁿ`-component of the `i`-th prism map: the affine realization of the simplicial degeneracy
`Fin.predAbove i`, sending vertex `ê_k` to `e_k` for `k ≤ i` and `e_{k-1}` for `k > i`. -/
noncomputable def prismAlpha {n : ℕ} (i : Fin (n + 1)) :
    C(stdSimplex ℝ (Fin (n + 2)), stdSimplex ℝ (Fin (n + 1))) :=
  affineSimplexStd (fun k => stdSimplex.vertex (Fin.predAbove i k))

/-- The `[0,1]`-component of the `i`-th prism map: the sum of the barycentric coordinates strictly
above `i` (so vertex `ê_k ↦ 0` for `k ≤ i`, `↦ 1` for `k > i`). -/
noncomputable def prismBeta {n : ℕ} (i : Fin (n + 1)) :
    C(stdSimplex ℝ (Fin (n + 2)), unitInterval) where
  toFun t := ⟨∑ k ∈ Finset.univ.filter (i.castSucc < ·), (t : Fin (n + 2) → ℝ) k, by
    refine ⟨Finset.sum_nonneg (fun k _ => t.2.1 k), ?_⟩
    calc ∑ k ∈ Finset.univ.filter (i.castSucc < ·), (t : Fin (n + 2) → ℝ) k
        ≤ ∑ k, (t : Fin (n + 2) → ℝ) k :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun k _ _ => t.2.1 k)
      _ = 1 := t.2.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_finset_sum _ (fun k _ => ?_)) _
    exact (continuous_apply k).comp continuous_subtype_val

/-! ## §2. The prism simplices and the prism operator -/

/-- The `i`-th prism `(n+1)`-simplex of `σ` under the homotopy `H : X × I → Y`: the affine prism
map `(prismAlpha i, prismBeta i) : Δⁿ⁺¹ → Δⁿ × I` post-composed with `σ × id` and then `H`. -/
noncomputable def prismSimplex {X Y : TopCat} {n : ℕ} (H : C(↑X × unitInterval, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) (i : Fin (n + 1)) :
    (TopCat.toSSet.obj Y).obj (op (SimplexCategory.mk (n + 1))) :=
  (Y.toSSetObjEquiv (op (SimplexCategory.mk (n + 1)))).symm
    (H.comp
      (((X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ).comp (prismAlpha i)).prodMk (prismBeta i)))

/-- The prism chain assigned to a single simplex `σ`: the ℤ/2-sum of its `n + 1` prism simplices
(over ℤ/2 the alternating signs `(-1)^i` of the integral prism all collapse to `1`). -/
noncomputable def prismBasis {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) : SingularChain Y (n + 1) :=
  ∑ i : Fin (n + 1), Finsupp.single (prismSimplex H σ i) 1

/-- **The prism operator** `P : Cₙ(X) → Cₙ₊₁(Y)`, the linear extension of `prismBasis` off the basis
simplices (`Finsupp.linearCombination`). It is the chain homotopy witnessing `f_# ≃ g_#`. -/
noncomputable def prismOp {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (n : ℕ) :
    SingularChain X n →ₗ[ZMod 2] SingularChain Y (n + 1) :=
  Finsupp.linearCombination (ZMod 2) (prismBasis H n)

@[simp] theorem prismOp_single {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y)) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) (a : ZMod 2) :
    prismOp H n (Finsupp.single σ a) = a • prismBasis H n σ := by
  rw [prismOp, Finsupp.linearCombination_single]

end SKEFTHawking.SingularPrism
