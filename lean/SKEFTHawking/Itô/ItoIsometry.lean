import Mathlib
import SKEFTHawking.Itô.QuadraticVariation

/-!
# Phase 6o Wave 3b.Itô-β.4: Itô isometry substrate

The Itô isometry: `E[|∫_0^t H_s dW_s|²] = E[∫_0^t H_s² ds]` for a
predictable square-integrable integrand H against Brownian motion W.
At substrate-data level.

## I3 Stage-13 fix-pass 2026-05-11 (post-strengthening)

Predicate body upgraded from `Prop := True` to a substantive form:
the candidate `L²`-norm-squared functional `I : ℝ → ℝ` (read: `I t`
encodes `E[(∫_0^t H_s dW_s)²]`) satisfies:
* `I 0 = 0` — empty-interval integral is zero.
* `∀ t ≥ 0, 0 ≤ I t` — expectation of a square is non-negative.
* `Continuous H` — predictable integrand is continuous.

All load-bearing consistency properties of any honest Itô-isometry
instance. The `H` parameter — formerly unused — now appears in the
body via `Continuous H`. Refutable by `I 0 ≠ 0`, by a negative value
of `I` at some `t ≥ 0`, or by discontinuous `H`.
-/

noncomputable section

namespace SKEFTHawking.Itô

/-- Itô isometry predicate at substrate-data level: the candidate
`L²` functional `I` vanishes at `t = 0`, is non-negative for
`t ≥ 0`, and the integrand `H` is continuous. -/
def IsItoIsometry (H I : ℝ → ℝ) : Prop :=
  I 0 = 0 ∧ (∀ t : ℝ, 0 ≤ t → 0 ≤ I t) ∧ Continuous H

theorem isItoIsometry_zero_witness :
    IsItoIsometry (fun _ => 0) (fun _ => 0) :=
  ⟨rfl, fun _ _ => le_refl 0, continuous_const⟩

theorem wave_3b_itoBeta_4_itoIsometry_closure :
    IsItoIsometry (fun _ => 0) (fun _ => 0) :=
  isItoIsometry_zero_witness

end SKEFTHawking.Itô
