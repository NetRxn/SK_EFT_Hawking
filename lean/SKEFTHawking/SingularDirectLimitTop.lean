import Mathlib

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5-dltop) — direct limit over an order with a top element

If the directed index has a **greatest element** `⊤`, the filtered colimit collapses onto the value there:
`Module.DirectLimit.of R ι G f ⊤ : G ⊤ → DirectLimit G f` is **bijective**. Every element factors through
`⊤` (`of_f` with `le_top`), and an equality `of ⊤ x = of ⊤ y` forces `x = y` because the only `j ≥ ⊤` is
`⊤` itself (`top_le_iff`), where the transition map is the identity (`DirectedSystem.map_self`).

For a compact manifold `M`, `univ` is the top compact (`TopologicalSpace.Compacts.instTopOfCompactSpace`),
so this collapses `Hᵏ_c(M) = colim_K Hᵏ(M|K)` onto `Hᵏ(M|univ) = Hᵏ(M, ∅) = Hᵏ(M)` and
`colim_K H_n(sub K)` onto `H_n(sub univ) = H_n(M)` — the endpoints of the Poincaré-duality ladder.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

namespace SKEFTHawking.SingularDirectLimitTop

open Module

variable {R : Type*} [Semiring R] {ι : Type*} [PartialOrder ι] [OrderTop ι] [DecidableEq ι]
  [IsDirectedOrder ι] (G : ι → Type*) [(i : ι) → AddCommGroup (G i)] [(i : ι) → Module R (G i)]
  (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j) [DirectedSystem G (fun i j h => ⇑(f i j h))]

/-- **The direct limit over an order with a top element collapses onto the top value**:
`Module.DirectLimit.of R ι G f ⊤` is bijective. -/
theorem of_top_bijective : Function.Bijective (DirectLimit.of R ι G f ⊤) := by
  constructor
  · -- injective
    intro x y hxy
    obtain ⟨j, hj, hfxy⟩ := DirectLimit.exists_eq_of_of_eq hxy
    have hjtop : j = ⊤ := top_le_iff.mp hj
    subst hjtop
    rw [DirectedSystem.map_self (f := fun i j h => ⇑(f i j h)) (i := ⊤) x,
      DirectedSystem.map_self (f := fun i j h => ⇑(f i j h)) (i := ⊤) y] at hfxy
    exact hfxy
  · -- surjective
    intro z
    refine DirectLimit.induction_on z (fun i x => ?_)
    exact ⟨f i ⊤ le_top x, DirectLimit.of_f⟩

end SKEFTHawking.SingularDirectLimitTop
