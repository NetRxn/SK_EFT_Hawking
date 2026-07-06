/-
# Phase 5q.H (E1 integral PD) — integral cap–chainIncl naturality (first rung of the PD cap-ladder)

The integral cap product commutes with the subspace inclusion `sub S ↪ X`: the front/back
Alexander–Whitney faces are natural in `simplexIncl` (`SingularEuclideanCapIsoInt.frontFace_simplexIncl`,
`SingularCapSupportInt.backFace_simplexInclInt`), so
  `a ⌢ (chainIncl c) = chainIncl ((pullbackCochainInt a) ⌢ c)`,
where `pullbackCochainInt S k a` precomposes the integral cochain `a` with `simplexIncl`. Integral mirror
of the mod-2 `SingularCapChainIncl.cap_chainIncl` — the foundational naturality rung of the integral
Poincaré-duality cap-iso cover-induction (the cap commutes with the local↪global inclusions the five-lemma
ladder is built from).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `native_decide`, no `maxHeartbeats`, no axiom.
-/
import Mathlib
import SKEFTHawking.IntCapProductInt
import SKEFTHawking.SingularEuclideanCapIsoInt
import SKEFTHawking.SingularCapSupportInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)

namespace SKEFTHawking.SingularCapChainInclInt

variable {X : TopCat} (S : Set X)

/-- **The integral cochain pullback** along `sub S ↪ X`: precompose with `simplexIncl`. -/
noncomputable def pullbackCochainInt (k : ℕ) (a : SingularCochainInt X k) : SingularCochainInt (sub S) k :=
  fun τ => a (simplexIncl S k τ)

@[simp] theorem pullbackCochainInt_apply (k : ℕ) (a : SingularCochainInt X k)
    (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k))) :
    pullbackCochainInt S k a τ = a (simplexIncl S k τ) := rfl

/-- **Integral cap–chainIncl naturality**: `a ⌢ (chainIncl c) = chainIncl ((pullbackCochainInt a) ⌢ c)`.
On a basis `sub S`-simplex `τ`, both sides are `a(simplexIncl (frontₖ τ)) • [simplexIncl (backₘ τ)]`
(`frontFace`/`backFace` commute with `simplexIncl`). -/
theorem capInt_chainIncl {k m : ℕ} (a : SingularCochainInt X k) (c : SingularChainInt (sub S) (k + m)) :
    capInt a (chainIncl S (k + m) c) = chainIncl S m (capInt (pullbackCochainInt S k a) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => rw [map_add, map_add, map_add, map_add, hc, hd]
  | single τ s =>
      rw [chainIncl_single, capInt_single_smul, capInt_single_smul, capBasisInt, capBasisInt,
        pullbackCochainInt_apply, SingularEuclideanCapIsoInt.frontFace_simplexIncl,
        SingularCapSupportInt.backFace_simplexInclInt, map_smul, map_smul, chainIncl_single]

end SKEFTHawking.SingularCapChainInclInt
