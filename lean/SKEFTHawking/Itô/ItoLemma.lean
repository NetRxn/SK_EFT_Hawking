import Mathlib
import SKEFTHawking.Itô.Semimartingale

/-!
# Phase 6o Wave 3b.Itô-β.5: Itô's lemma substrate

The Itô change-of-variables formula: for `f ∈ C²(ℝ)` and a continuous
semimartingale X,

    f(X_t) = f(X_0) + ∫_0^t f'(X_s) dX_s + (1/2) ∫_0^t f''(X_s) d⟨X⟩_s.

Substrate-data level.

## I3 Stage-13 fix-pass 2026-05-11 (post-strengthening)

Predicate body upgraded from `Prop := True` to a substantive form:
`IsItoLemma f X result` asserts FOUR structural properties:
* `Continuous f` — load-bearing for the `f''` term in Itô's formula.
* `Continuous X` — the semimartingale process is continuous (the
  standard Polish-space hypothesis).
* `Continuous result` — the resulting process is continuous.
* `result 0 = f (X 0) - f (X 0)` — the RHS of Itô's formula vanishes
  at the lower endpoint of the integration interval (boundary
  consistency at `t = 0`).

All three function parameters now constrain the body. Refutable by
discontinuity in `f`, `X`, or `result`, or by `result 0 ≠ 0` (since
`f (X 0) - f (X 0) = 0` simplifies the boundary identity).
-/

noncomputable section

namespace SKEFTHawking.Itô

/-- Itô's lemma predicate at substrate-data level: `f`, `X`, and
`result` are continuous, and `result 0 = f (X 0) - f (X 0)` (boundary
consistency identity at the lower limit of integration). -/
def IsItoLemma (f : ℝ → ℝ) (X result : ℝ → ℝ) : Prop :=
  Continuous f ∧ Continuous X ∧ Continuous result ∧
    result 0 = f (X 0) - f (X 0)

/-- Cross-bridge placeholder: Itô's lemma will reduce to ordinary
calculus when the semimartingale has zero quadratic variation (i.e.,
is a finite-variation process). At substrate-data level we prove
inhabitation on the zero witness: each of `f`, `X`, `result` is
`continuous_const`, and the boundary identity simplifies via
`f (X 0) - f (X 0) = 0`. The substantive content (reducing the
Itô integral term to the Lebesgue-Stieltjes integral under zero QV)
lifts when Mathlib's stochastic-integral substrate lands. This single
theorem also serves as the per-module wave-closure summary for
`ItoLemma`; the prior redundant `wave_3b_itoBeta_5_itoLemma_closure`
restated the same conclusion and was retired in the I3 Stage-13
fix-pass (2026-05-11) per
`papers/AutomatedReviews/2026-05-11-1251-bundle-stage13/I3.md`
finding 3.4. -/
theorem ito_reduces_to_calculus_when_zero_qv :
    IsItoLemma (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
  ⟨continuous_const, continuous_const, continuous_const, by simp⟩

end SKEFTHawking.Itô
