/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — the 𝕊₃ base-case coverage (toward unconditional discharge)

`KMMReductionDischarge.lean` reduces `Nonempty KMMReduction` to the single fact

  `coverage : ∀ M, IsCliffordTRealizable M → μ(M) ≤ 3 → ∃ gs, interp gs = M ∧ gs.length ≤ 9`

(every realizable matrix with squared-modulus sde `μ(M) ≤ 3` has a `≤ 9`-gate word —
KMM's finite `𝕊₃` base orbit, `N₃ = 9`, `1664` matrices). This file builds toward
proving it. **The finiteness key (no real-order machinery needed):** the cleared
column-0 numerators satisfy `P_x + P_y = 2^s ≤ 4` with `P_x = a²+b²+c²+d²` a *sum of
squares ≥ 0*, so each `P ≤ 4` and every numerator coordinate is bounded by `2`.

  * `ZOmegaSqrt2.denExp_le_two_of_denExp_normSq_le_three` — `denExp(|z|²) ≤ 3 ⟹
    denExp z ≤ 2` (any entry; generalises the `M₀₀`-only `MuDecrease` lemma).
  * `KMM.column0_cleared_bounded` — for a `μ ≤ 3` unitary, clearing column `0` at
    exponent `2` gives `ℤ[ω]` numerators `x, y` with `(|x|²).d ≤ 4` and `(|y|²).d ≤ 4`
    (hence bounded coordinates) — the finite-candidate seed for the `𝕊₃` enumeration.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.MuDecrease
import SKEFTHawking.FKLW.RossSelinger.UnitaryClosure

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmegaSqrt2

/-- **Bounded denominator for any low-sde entry**: `denExp(|z|²) ≤ 3 ⟹ denExp z ≤ 2`.
(`μ = 2·denExp z − gde(|x|²)`, `gde ≤ 1`, so `2·denExp z ≤ μ + 1 ≤ 4`.) Generalises
`KMM.denExp_le_two_of_muMeasure_le_three` from `M₀₀` to an arbitrary entry. -/
theorem denExp_le_two_of_denExp_normSq_le_three {z : ZOmegaSqrt2} (h : denExp (normSq z) ≤ 3) :
    denExp z ≤ 2 := by
  by_cases hd : denExp z ≤ 1
  · omega
  · have hd2 : 2 ≤ denExp z := by omega
    obtain ⟨x, hx, hg, hμ⟩ := entry_cleared_form hd2
    omega

end ZOmegaSqrt2

namespace KMM

open ZOmegaSqrt2

/-- **Finite-candidate seed for the `𝕊₃` base case**: for a `μ(M) ≤ 3` unitary, both
column-`0` entries clear at exponent `2` (`denExp ≤ 2`) into `ℤ[ω]` numerators `x, y`
whose squared-modulus rational parts satisfy `(|x|²).d ≤ 4` and `(|y|²).d ≤ 4`. Since
`(|x|²).d = a²+b²+c²+d²` is a sum of squares, this bounds every coordinate by `2`, so
the `μ ≤ 3` column-`0` data ranges over a finite explicit set.

Proof: `denExp(M₀₀) = denExp(M₁₀) ≤ 2` (`denExp_normSq_col0_eq` + the bound); clear both
at exponent `2` (`denExp_le_iff`); `|x|² + |y|² = √2^(2·2) = 2²` (`clearedCol_normSq_sum`
+ `sqrt2_pow_two_mul_coords`), so `(|x|²).d + (|y|²).d = 4` with both `≥ 0`. -/
theorem column0_cleared_bounded {M : Mat2} (hu : IsUnitaryT M) (h : muMeasure M ≤ 3) :
    ∃ x y : ZOmega, (sqrt2 : ZOmegaSqrt2) ^ 2 * M 0 0 = of x ∧
      (sqrt2 : ZOmegaSqrt2) ^ 2 * M 1 0 = of y ∧
      (ZOmega.normSq x).d ≤ 4 ∧ (ZOmega.normSq y).d ≤ 4 := by
  have hcol : denExp (normSq (M 0 0)) = denExp (normSq (M 1 0)) := denExp_normSq_col0_eq hu
  have hd0 : denExp (M 0 0) ≤ 2 :=
    denExp_le_two_of_denExp_normSq_le_three (by unfold muMeasure at h; omega)
  have hd1 : denExp (M 1 0) ≤ 2 :=
    denExp_le_two_of_denExp_normSq_le_three (by unfold muMeasure at h; omega)
  obtain ⟨x, hx⟩ := denExp_le_iff.mp hd0
  obtain ⟨y, hy⟩ := denExp_le_iff.mp hd1
  have h1 : normSq (M 0 0) + normSq (M 1 0) = 1 := unitary_col0_normSq hu
  have hsum := clearedCol_normSq_sum hx hy h1
  obtain ⟨_, hd⟩ := ZOmega.sqrt2_pow_two_mul_coords 2
  have hPsum : (ZOmega.normSq x).d + (ZOmega.normSq y).d = 4 := by
    have e := congrArg ZOmega.d hsum
    rw [ZOmega.add_d, hd] at e; norm_num at e; exact e
  have hPx : 0 ≤ (ZOmega.normSq x).d := by rw [ZOmega.normSq_d]; positivity
  have hPy : 0 ≤ (ZOmega.normSq y).d := by rw [ZOmega.normSq_d]; positivity
  exact ⟨x, y, hx, hy, by omega, by omega⟩

end KMM

end SKEFTHawking.RossSelinger
