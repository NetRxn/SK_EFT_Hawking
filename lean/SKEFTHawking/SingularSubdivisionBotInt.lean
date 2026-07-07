/-
# Phase 5q.H (E1 CSC-PD tower) — the integral degree-0 subdivision pack

Integral (`ZMod 2 → ℤ`) mirror of the degree-0 slice of `SingularSubdivisionBot`. The barycentric
subdivision of a point is itself, so `Sd = id` on `0`-chains — a clean identity over ℤ (no sign collapse,
unlike the mod-2 `iterHomotopy_chainHomotopy₀` which relied on `x + x = 0`). This is the base leaf of the
integral `H₀`-excision/MV-exactness mirror chain (`relative_small_boundary₀Int` → `excisionMap_injective₀Int`
→ `mv_exact_middle₀Int` → the D⁰ five-lemma).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSubdivisionInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularAffineChainInt (linSubdivInt_zero)
open SKEFTHawking.SingularExcisionPushforward (pushSimplexM_vertices)
open SKEFTHawking.SingularSubdivisionInt

namespace SKEFTHawking.SingularSubdivisionBotInt

/-- `pushChainMInt` of the identity `0`-simplex chain is the singleton chain (degree-0 companion of
`pushChainMInt_idChainInt`). -/
theorem pushChainMInt_idChain₀ {X : TopCat}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 0))) :
    pushChainMInt σ (idChainInt 0) = Finsupp.single σ 1 := by
  rw [idChainInt, pushChainMInt_single, pushSimplexM_vertices]

/-- **`Sd = id` on `0`-chains** (integral): the barycentric subdivision of a point is itself. -/
theorem singularSdInt_zero {X : TopCat} (c : SingularChainInt X 0) : singularSdInt X 0 c = c := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero]
  | add c d hc hd => rw [map_add, hc, hd]
  | single σ a =>
    rw [show (Finsupp.single σ a : SingularChainInt X 0) = a • Finsupp.single σ 1 from by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one],
      map_smul, singularSdInt_single, linSubdivInt_zero, pushChainMInt_idChain₀]

/-- `Sdᵐ = id` on `0`-chains (integral). -/
theorem singularSdInt_iterate_zero_degree {X : TopCat} (m : ℕ) (c : SingularChainInt X 0) :
    (⇑(singularSdInt X 0))^[m] c = c := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, singularSdInt_zero]

end SKEFTHawking.SingularSubdivisionBotInt
