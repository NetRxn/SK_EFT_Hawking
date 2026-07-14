import Mathlib
import SKEFTHawking.RP4CupLadder
import SKEFTHawking.RP4Witness
import SKEFTHawking.SingularPD4Instances

/-!
# Phase 5q.G (B-arc, M4-a,b) — the Wu assembly on `ℝP⁴`: `μ(x⁴) = 1` and `v₂ = x²`

The M3 ladder (`Hᵏ(ℝP⁴) = span{xpow k}`, `xpow k ≠ 0`, `xpow 4 = x² ⌣ x²`) feeds the genuine
PD data of the closed charted `ℝP⁴` (`poincareDual4Mid_of_closed`):

* **`μ(x² ⌣ x²) = 1`** — non-degeneracy gives a witness `w` with `μ(x² ⌣ w) = 1`; the span
  forces `w = c • x²`, and `c · μ(x²⌣x²) ≠ 0` pins both factors.
* **`v₂ = x²`** — the middle Wu class is the unique class pairing as the square functional;
  `x²` satisfies the same relation on the span (`c² = c` over `ℤ/2`), so injectivity closes.

With `v₁ = x` (M4-c, the Bockstein) these discharge both `ℝP⁴` hypotheses of THE REDUCTION.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.RP4PointSet SKEFTHawking.RP4CohomologyLadder SKEFTHawking.RP4CupLadder
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.PoincareDualityWu SKEFTHawking.SingularPD4Instances
open SKEFTHawking.RP4Witness

namespace SKEFTHawking.RP4WuAssembly

/-- **`μ(x² ⌣ x²) = 1`** — the top cup-square of the degree-2 ladder generator pairs to `1`
against the fundamental class: non-degeneracy plus the one-dimensionality of `H²`. -/
theorem mu_cupH24_xpow2_xpow2 :
    (poincareDual4Mid_of_closed (M := RP4)).mu (cupH24 (xpow 2) (xpow 2)) = 1 := by
  have h2ne : xpow 2 ≠ 0 := xpow_ne_zero (by norm_num)
  have hfne : (cupH24 (X := TopCat.of RP4)).compr₂
      (poincareDual4Mid_of_closed (M := RP4)).mu (xpow 2) ≠ 0 := by
    intro h
    exact h2ne ((poincareDual4Mid_of_closed (M := RP4)).nondeg (by rw [h, map_zero]))
  have hex : ∃ w, (poincareDual4Mid_of_closed (M := RP4)).mu (cupH24 (xpow 2) w) ≠ 0 := by
    by_contra hall
    push Not at hall
    refine hfne (LinearMap.ext fun w => ?_)
    rw [LinearMap.compr₂_apply, LinearMap.zero_apply]
    exact hall w
  obtain ⟨w, hw⟩ := hex
  obtain ⟨c, rfl⟩ := cohomology_eq_smul_xpow (by norm_num) w
  rw [map_smul, map_smul, smul_eq_mul] at hw
  revert hw
  generalize (poincareDual4Mid_of_closed (M := RP4)).mu (cupH24 (xpow 2) (xpow 2)) = m
  revert c m
  decide

/-- **`μ(xpow 4) = 1`** — the top ladder class pairs to `1` (via `xpow 4 = x² ⌣ x²`). -/
theorem mu_xpow_four :
    (poincareDual4Mid_of_closed (M := RP4)).mu (xpow 4) = 1 := by
  rw [xpow_four_eq_cupH24]
  exact mu_cupH24_xpow2_xpow2

/-- **`v₂ = x²`** — the middle Wu class of `ℝP⁴` is the degree-2 ladder generator: both pair
identically against the one-dimensional `H²` (`c² = c` over `ℤ/2` absorbs the quadratic/linear
mismatch), and the pairing is injective. -/
theorem wuClass2_eq_xpow2 :
    wuClass2 (poincareDual4Mid_of_closed (M := RP4)) = xpow 2 := by
  apply (poincareDual4Mid_of_closed (M := RP4)).nondeg
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply, wu_relation]
  obtain ⟨c, rfl⟩ := cohomology_eq_smul_xpow (by norm_num) w
  rw [show cupSquare2 (c • xpow 2) = cupH24 (c • xpow 2) (c • xpow 2) from rfl]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  generalize (poincareDual4Mid_of_closed (M := RP4)).mu (cupH24 (xpow 2) (xpow 2)) = m
  revert m c
  decide

/-- **The cup-square functional collapses onto `x²`** — for every `a ∈ H²(ℝP⁴;ℤ/2)`,
`μ(a ⌣ a) = μ(a ⌣ x²)`: on the rank-1 `H²` (`a = c • x²`), `c² = c` over `ℤ/2` absorbs the
quadratic/linear mismatch (the `wuClass2_eq_xpow2` pattern — this is the Wu relation at
`v₂ = x²`, restated pointwise). The bridge from the abstract `hchar` cup-square form to the
`hchar_pairing` `⌣ x²` form on `ℝP⁴`. -/
theorem mu_cupH24_self_eq_cupH24_xpow2 (a : Cohomology (TopCat.of RP4) 2) :
    (poincareDual4Mid_of_closed (M := RP4)).mu (cupH24 a a)
      = (poincareDual4Mid_of_closed (M := RP4)).mu (cupH24 a (xpow 2)) := by
  obtain ⟨c, rfl⟩ := cohomology_eq_smul_xpow (by norm_num) a
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  generalize (poincareDual4Mid_of_closed (M := RP4)).mu (cupH24 (xpow 2) (xpow 2)) = m
  revert m c
  decide

end SKEFTHawking.RP4WuAssembly
