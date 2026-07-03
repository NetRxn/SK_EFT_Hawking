import Mathlib
import SKEFTHawking.SingularSubdivision

/-!
# Phase 5q.G (G1 PD-induction, D⁰-substrate) — the degree-0 subdivision pack

The degree-0 instances of the barycentric-subdivision machinery, all degenerate by the affine
bottom facts (`linSubdiv 0 = id`, `linHomotopy 0 = 0`, both `rfl`):

* `singularSd_zero` — `Sd = id` on `0`-chains (the subdivision of a point is itself);
* `singularD_zero` — the subdivision homotopy vanishes on `0`-chains;
* `singularSd_iterate_zero_degree` — `Sdᵐ = id` on `0`-chains;
* `iterHomotopy_degree_zero` — the iterated homotopy vanishes on `0`-chains;
* `iterHomotopy_chainHomotopy₀` — **THE bottom chain-homotopy identity**
  `∂(Dₘc) = c + Sdᵐc` for `0`-chains (both sides vanish over `ℤ/2`) — the degree-0 companion of
  `iterHomotopy_chainHomotopy` (whose statement is floored at chains of degree `n+1`), and the
  single primitive the whole `H₀`-excision/MV-exactness mirror chain rests on.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularExcisionMod2 SKEFTHawking.SingularHomologyMod2
  SKEFTHawking.SingularSubdivision SKEFTHawking.SingularSubdivisionNatural
  SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularExcisionPushforward

namespace SKEFTHawking.SingularSubdivisionBot

/-- `pushChainM` of the identity `0`-simplex chain is the singleton chain (degree-0 companion of
`pushChainM_idChain`). -/
theorem pushChainM_idChain₀ {X : TopCat}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 0))) :
    pushChainM σ (idChain 0) = Finsupp.single σ 1 := by
  rw [idChain, pushChainM_single, pushSimplexM_vertices]

/-- **`Sd = id` on `0`-chains**: the barycentric subdivision of a point is itself. -/
theorem singularSd_zero {X : TopCat} (c : SingularChain X 0) : singularSd X 0 c = c := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero]
  | add c d hc hd => rw [map_add, hc, hd]
  | single σ a =>
    rw [show (Finsupp.single σ a : SingularChain X 0) = a • Finsupp.single σ 1 from by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one],
      map_smul, singularSd_single, linSubdiv_zero, pushChainM_idChain₀]

/-- **The subdivision homotopy vanishes on `0`-chains** (`linHomotopy 0 = 0`). -/
theorem singularD_zero {X : TopCat} (c : SingularChain X 0) : singularD X 0 c = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => rw [map_zero]
  | add c d hc hd => rw [map_add, hc, hd, add_zero]
  | single σ a =>
    rw [show (Finsupp.single σ a : SingularChain X 0) = a • Finsupp.single σ 1 from by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one],
      map_smul, singularD_single, linHomotopy_zero_map, map_zero, smul_zero]

/-- `Sdᵐ = id` on `0`-chains. -/
theorem singularSd_iterate_zero_degree {X : TopCat} (m : ℕ) (c : SingularChain X 0) :
    (⇑(singularSd X 0))^[m] c = c := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, singularSd_zero]

/-- The iterated homotopy vanishes on `0`-chains. -/
theorem iterHomotopy_degree_zero {X : TopCat} (m : ℕ) (c : SingularChain X 0) :
    iterHomotopy X 0 m c = 0 := by
  rw [iterHomotopy]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [singularD_zero c]
  exact Function.iterate_fixed (map_zero _) i

/-- **THE bottom chain-homotopy identity**: `∂(Dₘc) = c + Sdᵐc` for a `0`-chain `c` — no
`Dₘ(∂c)`-correction (there is no degree below `0`); over `ℤ/2` both sides vanish. -/
theorem iterHomotopy_chainHomotopy₀ {X : TopCat} (m : ℕ) (c : SingularChain X 0) :
    chainBoundary X 0 (iterHomotopy X 0 m c)
      = c + (⇑(singularSd X 0))^[m] c := by
  rw [iterHomotopy_degree_zero, map_zero, singularSd_iterate_zero_degree]
  exact (ZModModule.add_self c).symm

end SKEFTHawking.SingularSubdivisionBot
