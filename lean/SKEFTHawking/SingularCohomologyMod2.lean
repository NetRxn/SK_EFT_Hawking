/-
# Phase 5q.F — singular ℤ/2 cohomology (toward the ABK β built from the bordism group)

The β bottleneck of the genuine Smith-LES endpoint: a homomorphism `β : DataBordismGrp ξ_Pin⁺ →+ ℤ/16`
(the ABK invariant) **built from the bordism group**, not supplied as a hypothesis
(`PinPlusBordismGroupDerived.dataBordism_iso_zmod16` takes it as one). That needs the ℤ/2 cohomology of
the underlying `SingularManifold` spaces — which Mathlib lacks (it has the singular *chain* complex,
`AlgebraicTopology.singularChainComplexFunctor`, but no singular cohomology). This module builds it
elementarily on Mathlib's singular simplicial set `TopCat.toSSet`: singular `n`-cochains are `ℤ/2`-valued
functions on singular `n`-simplices, with the coboundary the alternating (mod 2: plain) sum over faces.

First brick: the singular cochain group and the coboundary `δ`. The `δ² = 0` identity (from the
cosimplicial relations `SimplexCategory.δ_comp_δ`), cohomology `Hⁿ`, the cup product (Alexander–Whitney),
and the cellular-comparison computations follow.
-/
import Mathlib

namespace SKEFTHawking.SingularCohomologyMod2

open CategoryTheory Opposite

/-- **Singular `n`-cochains** of a space `X` with `ℤ/2` coefficients: `ℤ/2`-valued functions on the
singular `n`-simplices `(TopCat.toSSet.obj X).obj (op [n])` (continuous maps `Δⁿ → X`). A genuine
`ℤ/2`-vector space (a Pi type over the field `ZMod 2`). -/
abbrev SingularCochain (X : TopCat) (n : ℕ) : Type :=
  (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)) → ZMod 2

/-- The `i`-th face of a singular `(n+1)`-simplex `σ`: precompose with the `i`-th coface `δ i`. -/
noncomputable def face {X : TopCat} {n : ℕ} (i : Fin (n + 2))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)) :=
  (TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ

/-- The **singular coboundary** `δ : Cⁿ → Cⁿ⁺¹`, `(δ f)(σ) = ∑ᵢ f(∂ᵢ σ)` over `ℤ/2` (the alternating
sign is `+1` mod 2). Genuine `ℤ/2`-linear (a sum of precompositions). -/
noncomputable def coboundary (X : TopCat) (n : ℕ) (f : SingularCochain X n) : SingularCochain X (n + 1) :=
  fun σ => ∑ i : Fin (n + 2), f (face i σ)

end SKEFTHawking.SingularCohomologyMod2
