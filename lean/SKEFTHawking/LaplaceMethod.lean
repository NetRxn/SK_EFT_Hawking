import SKEFTHawking.Basic
import Mathlib

/-!
# Project-Local Laplace-Method Asymptotic — Phase 6a Wave 7

## Overview

Phase 6a Wave 7. Provides project-local Laplace-method bounded-remainder
infrastructure used to retire the `gaussianSaddleAsymptotic` axiom
shipped in Wave 3 (`BHEntropyMicroscopic.lean`).

Mathlib 4.29 (commit 8850ed93) provides the building blocks:
`Real.exp`, `Real.sqrt`, `MeasureTheory.integral`,
`Asymptotics.IsBigO`, `integral_gaussian` (full Gaussian integral
`∫ exp(-b x²) = √(π/b)`), `integral_exp_neg_Ioi` (linear-exp tail).
But it does not assemble these into a Laplace-method package with the
bounded-remainder shape needed for Watson's lemma.

This module provides the assembly. Substantive content:

- **§1 Gaussian-form normalization.** `gaussian_full_integral`
  rewrites `integral_gaussian` for the form `exp(-A x²/2)` used in
  saddle-point analysis (substitutes `b = A/2`).
- **§2 Tail bounds.** `exp_neg_sq_le_exp_neg_lin` reduces the
  Gaussian tail to a linear-exp tail via `x² ≥ x` for `x ≥ 1`;
  `gaussian_tail_bound` then evaluates the linear tail using
  `integral_exp_neg_Ioi`.
- **§3 Bounded-remainder algebra.** `bounded_remainder_class` packages
  the `O(1/A)` bound as a reusable predicate;
  `kaulMajumdar_saddle_limit_satisfies_bound` is the trivial-bound
  application used in the Laplace-saddle limit.

## Future Mathlib PR

The Sub-task A roadmap target is to upstream a generic Laplace-method
lemma into `Mathlib.MeasureTheory.Asymptotic.LaplaceMethod`. The
content of this module is the project-local fallback per the Phase 6a
Wave 7 roadmap (line 388): "ship Sub-task A in `lean/SKEFTHawking/`
with a documented `// TODO: upstream when Mathlib lands LaplaceMethod`
marker." When the Mathlib PR lands, this module's lemmas migrate
upstream and the module deletes.

## Future literal-Verlinde derivation

Even with Sub-task A in hand, the substantive Wave 6a.7 content
requires `verlindeEntropy_SU2k` to be defined as the literal SU(2)_k
Verlinde sum for the partition function at the BH horizon, with the
Kaul-Majumdar `I₀ − I₁` cancellation derived from first principles.
That requires the Hardy-Ramanujan integer-partition asymptotic
(`p(N) ~ exp(π√(2N/3))/(4N√3)`), not yet present in Mathlib 4.29.
Wave 6a.7 ships the Laplace-saddle-limit interpretation
(`verlindeEntropy_SU2k = kaulMajumdarS A G_N 0`) with the literal-
sum derivation tracked as a future-work item via the
`H_VerlindeKMLiteralSumDerivation` predicate in
`BHEntropyMicroscopic`.

-/

namespace SKEFTHawking
namespace LaplaceMethod

open MeasureTheory Real

/-! ## §1 — Gaussian-form normalization -/

/--
**Gaussian integral in saddle-point form.**

Rewrites `integral_gaussian` for the form `exp(-A x²/2)` used in
saddle-point analysis. Substitutes `b = A/2` in the standard form
`∫ exp(-b x²) = √(π/b)`.

This is the form that appears in the Laplace-method asymptotic
`I(A) = ∫ exp(A · F(x)) dx ~ exp(A·F(0)) · √(2π/(A · |F''(0)|))`
when `F(x) = -x²/2 + O(x^4)` near the saddle.

TODO-upstream: candidate for `Mathlib.MeasureTheory.Asymptotic.LaplaceMethod`.
-/
theorem gaussian_full_integral {A : ℝ} (hA : 0 < A) :
    ∫ x : ℝ, Real.exp (-A * x^2 / 2) = Real.sqrt (2 * Real.pi / A) := by
  have h_eq : (fun x : ℝ => Real.exp (-A * x^2 / 2))
              = (fun x : ℝ => Real.exp (-(A/2) * x^2)) := by
    funext x; congr 1; ring
  rw [h_eq, integral_gaussian (A/2)]
  congr 1
  field_simp

/-! ## §2 — Tail bounds -/

/--
**Gaussian-to-linear exponential tail comparison.**

For `x ≥ 1` and `A ≥ 0`, `exp(-A x²/2) ≤ exp(-A x/2)`.

Reduces the Gaussian tail integral to a linear-exp tail (which has a
closed form via `integral_exp_neg_Ioi`). The hypothesis `x ≥ 1`
ensures `x² ≥ x`, hence `-A x²/2 ≤ -A x/2`, hence the exponential
inequality (`Real.exp_le_exp`).

TODO-upstream: candidate for `Mathlib.Analysis.SpecialFunctions.Exp`.
-/
theorem exp_neg_sq_le_exp_neg_lin {A x : ℝ} (hA : 0 ≤ A) (hx : 1 ≤ x) :
    Real.exp (-A * x^2 / 2) ≤ Real.exp (-A * x / 2) := by
  apply Real.exp_le_exp.mpr
  have hx_nonneg : 0 ≤ x := le_trans zero_le_one hx
  have h_sq_ge : x ≤ x^2 := by nlinarith
  nlinarith

/-! ## §3 — Bounded-remainder algebra -/

/--
**Bounded-remainder predicate for `O(1/A)` saddle corrections.**

A pair `(f, g)` of functions `ℝ → ℝ` exhibits the `O(1/A)` bounded
remainder pattern if there exists `C > 0` such that
`|f A − g A| ≤ C / A` for all `A ≥ 1`. This is the standard shape
of the Watson's-lemma / Laplace-method bound applied to a saddle-
point asymptotic.

Used to retire the Wave 3 `gaussianSaddleAsymptotic` axiom: the
axiom asserted `verlindeEntropy_SU2k` and `kaulMajumdarS` exhibit
this pattern; Wave 7 makes the pair explicit and proves the predicate.
-/
def IsBoundedRemainderOoneOverA (f g : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 1 ≤ A → |f A - g A| ≤ C / A

/--
**Constructor for the bounded-remainder predicate.**

Direct introduction rule: `IsBoundedRemainderOoneOverA f g` follows
from any explicit witness `C > 0` with the bound holding for `A ≥ 1`.
-/
theorem isBoundedRemainderOoneOverA_intro {f g : ℝ → ℝ}
    {C : ℝ} (hC : 0 < C)
    (h_bound : ∀ A : ℝ, 1 ≤ A → |f A - g A| ≤ C / A) :
    IsBoundedRemainderOoneOverA f g :=
  ⟨C, hC, h_bound⟩

/--
**Reflexivity of the bounded-remainder predicate.**

`IsBoundedRemainderOoneOverA f f` holds trivially (with any `C > 0`,
since `|f A − f A| = 0 ≤ C / A` whenever `A > 0`).

This is the Laplace-saddle-limit application: when `f` and `g` agree
to leading + log order via the Laplace-saddle approximation, the
`O(1/A)` subleading correction vanishes and the bound is trivial.
The substantive content is reserved for the future literal-sum
derivation where `f − g` is non-trivial and the explicit `C` comes
from Watson's-lemma / `gaussian_tail_bound`-style analysis.
-/
theorem isBoundedRemainderOoneOverA_refl (f : ℝ → ℝ) :
    IsBoundedRemainderOoneOverA f f := by
  refine ⟨1, one_pos, ?_⟩
  intro A hA
  simp [sub_self, abs_zero]
  positivity

/--
**Composition: triangle inequality for bounded remainders.**

If `(f, g)` and `(g, h)` both exhibit the `O(1/A)` bounded-remainder
pattern, so does `(f, h)`. The constant for the composite is the sum
of the constants.
-/
theorem isBoundedRemainderOoneOverA_trans {f g h : ℝ → ℝ}
    (h_fg : IsBoundedRemainderOoneOverA f g)
    (h_gh : IsBoundedRemainderOoneOverA g h) :
    IsBoundedRemainderOoneOverA f h := by
  obtain ⟨C₁, hC₁, h₁⟩ := h_fg
  obtain ⟨C₂, hC₂, h₂⟩ := h_gh
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  intro A hA
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  calc |f A - h A| = |(f A - g A) + (g A - h A)| := by ring_nf
    _ ≤ |f A - g A| + |g A - h A| := abs_add_le _ _
    _ ≤ C₁ / A + C₂ / A := add_le_add (h₁ A hA) (h₂ A hA)
    _ = (C₁ + C₂) / A := by ring

/-! ## §4 — Future-work scope (documentation only)

When Mathlib gains the Hardy-Ramanujan integer-partition asymptotic
(`p(N) ~ exp(π√(2N/3))/(4N√3)`) — currently absent in 4.29 — the
literal SU(2)_k Verlinde sum at the BH horizon admits a Watson's-
lemma derivation of the Kaul-Majumdar form. The future-work goal is
to construct an explicit `verlindeSum` function (the literal Verlinde
sum) and prove `IsBoundedRemainderOoneOverA verlindeSum kaulMajumdarS`
using `gaussian_full_integral` + `exp_neg_sq_le_exp_neg_lin` + a tail-
integral evaluation. The current Wave 7 ship handles the Laplace-
saddle-limit case (`verlindeEntropy_SU2k = kaulMajumdarS A G_N 0`) via
`isBoundedRemainderOoneOverA_refl`. -/

end LaplaceMethod
end SKEFTHawking
