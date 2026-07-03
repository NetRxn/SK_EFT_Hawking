import Mathlib
import SKEFTHawking.SingularRelCohomVanishAbove

/-!
# Phase 5q.F (w₂-foundation, G1 PD track A) — colimit top-degree vanishing of `Hᵏ_c(W)`

The compactly-supported cohomology `Hᵏ_c(W) = colim_{K ⊆ W compact} Hᵏ(M|K)`
(`SingularCompactlySupportedOpen`) vanishes as soon as its directed system vanishes **on a cofinal
family of stages**: every class of the colimit is `of K a` for some stage `K`
(`Module.DirectLimit.induction_on`), pushes into a vanishing stage `K' ≥ K` along the transition map
(`Module.DirectLimit.of_f`), and dies there.

* `cscOpen_eq_zero_of_cofinal_vanish` — the clean general lemma (abstract cofinal-vanishing
  hypothesis).
* `cscOpen_eq_zero_of_stage_vanish` — the everywhere-stage-wise special case.
* `cscOpen_eq_zero_of_vanishAbove_cofinal` — the composition with relative universal coefficients
  (`SingularRelCohomVanishAbove.cohomGW_eq_zero_of_vanishAbove`): if every compact in `W` is
  contained in a compact `K'` with `vanishAbove n ↑K'` (the Hatcher-3.27 homology vanishing), then
  `Hᵏ_c(W) = 0` for every `k > n` — the top-degree vanishing of the Poincaré-duality open-cover
  induction.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularManifoldFundamentalClass SKEFTHawking.SingularCompactsInOpen
  SKEFTHawking.SingularCompactlySupportedOpen SKEFTHawking.SingularRelCohomVanishAbove

namespace SKEFTHawking.SingularCSCVanishAbove

variable {M : TopCat}

/-- **Colimit vanishing from cofinal stage vanishing**: if every stage `K` of the `Hᵏ_c(W)` directed
system admits a later stage `K' ≥ K` on which every element vanishes, then every element of the
colimit `Hᵏ_c(W)` is `0`. `Module.DirectLimit.induction_on` presents a class as `of K a`;
`Module.DirectLimit.of_f` pushes it to `of K' (cohomFW … a) = of K' 0 = 0`. -/
theorem cscOpen_eq_zero_of_cofinal_vanish {W : Set ↑M} {k : ℕ}
    (h : ∀ K : CompactsIn W, ∃ K' : CompactsIn W, K ≤ K' ∧ ∀ x : cohomGW W k K', x = 0)
    (α : CompactlySupportedCohomologyOpen W k) : α = 0 := by
  refine Module.DirectLimit.induction_on α (fun K a => ?_)
  obtain ⟨K', hKK', hvan⟩ := h K
  rw [← Module.DirectLimit.of_f (hij := hKK') (x := a), hvan (cohomFW W k K K' hKK' a), map_zero]
  exact rfl

/-- **Colimit vanishing from everywhere-stage vanishing**: if every stage object `cohomGW W k K` of
the `Hᵏ_c(W)` system is trivial, so is the colimit. The `K' = K` instance of the cofinal lemma. -/
theorem cscOpen_eq_zero_of_stage_vanish {W : Set ↑M} {k : ℕ}
    (h : ∀ (K : CompactsIn W) (x : cohomGW W k K), x = 0)
    (α : CompactlySupportedCohomologyOpen W k) : α = 0 :=
  cscOpen_eq_zero_of_cofinal_vanish (fun K => ⟨K, le_refl K, h K⟩) α

/-- **Top-degree vanishing of `Hᵏ_c(W)` from `vanishAbove` on a cofinal family**: if every compact
`K ⊆ W` is contained in a compact `K' ⊆ W` satisfying the Hatcher-3.27 homology vanishing
`vanishAbove n ↑K'` (`Hᵢ(M|K') = 0` for `i > n`), then `Hᵏ_c(W) = 0` for every degree `k > n`.
Universal coefficients turns each `vanishAbove` stage into cohomology vanishing
(`cohomGW_eq_zero_of_vanishAbove`); the cofinal colimit lemma finishes. -/
theorem cscOpen_eq_zero_of_vanishAbove_cofinal {n : ℕ} {W : Set ↑M} {k : ℕ} (hk : n < k)
    (h : ∀ K : CompactsIn W, ∃ K' : CompactsIn W, K ≤ K' ∧ vanishAbove n (↑K'.1 : Set ↑M))
    (α : CompactlySupportedCohomologyOpen W k) : α = 0 := by
  refine cscOpen_eq_zero_of_cofinal_vanish (fun K => ?_) α
  obtain ⟨K', hKK', hva⟩ := h K
  exact ⟨K', hKK', fun x => cohomGW_eq_zero_of_vanishAbove hk K' hva x⟩

end SKEFTHawking.SingularCSCVanishAbove
