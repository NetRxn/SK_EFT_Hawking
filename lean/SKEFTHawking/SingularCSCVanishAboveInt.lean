/-
# Phase 5q.H (E1 CSC-PD tower) — colimit vanishing of `Hᵏ_c(W;ℤ)` from cofinal stage vanishing

Integral (`ZMod 2 → ℤ`) mirror of `SingularCSCVanishAbove.cscOpen_eq_zero_of_cofinal_vanish`. The
compactly-supported cohomology `Hᵏ_c(W;ℤ) = colim_{K ⊆ W} Hᵏ(M|K;ℤ)` vanishes as soon as its directed
system vanishes on a **cofinal family of stages**: every colimit class is `of K a`
(`Module.DirectLimit.induction_on`), pushes into a vanishing stage `K' ≥ K` (`Module.DirectLimit.of_f`),
and dies there. The `DirectLimit` API is coefficient-agnostic; only the objects/maps are the integral
`cohomGWInt`/`cohomFWInt`.

The cofinal-vanishing driver of the base-case B3 CSC-vanishing (`cscOpen_eq_zero_of_chartConvexInt`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCompactlySupportedOpenInt

open SKEFTHawking.SingularCompactsInOpen SKEFTHawking.SingularCompactlySupportedOpenInt

namespace SKEFTHawking.SingularCSCVanishAboveInt

variable {M : TopCat}

/-- **Colimit vanishing from cofinal stage vanishing** (integral): if every stage `K` of the `Hᵏ_c(W;ℤ)`
directed system admits a later stage `K' ≥ K` on which every element vanishes, then every element of the
colimit `Hᵏ_c(W;ℤ)` is `0`. -/
theorem cscOpen_eq_zero_of_cofinal_vanishInt {W : Set ↑M} {k : ℕ}
    (h : ∀ K : CompactsIn W, ∃ K' : CompactsIn W, K ≤ K' ∧ ∀ x : cohomGWInt W k K', x = 0)
    (α : CompactlySupportedCohomologyOpenInt W k) : α = 0 := by
  refine Module.DirectLimit.induction_on α (fun K a => ?_)
  obtain ⟨K', hKK', hvan⟩ := h K
  rw [← Module.DirectLimit.of_f (hij := hKK') (x := a), hvan (cohomFWInt W k K K' hKK' a), map_zero]
  exact rfl

end SKEFTHawking.SingularCSCVanishAboveInt
