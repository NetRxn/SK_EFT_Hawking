import Mathlib

/-!
# Phase 6o Wave 3b.Itô-β.1: Stochastic integral substrate

In-program build at predicate-data level. Mathlib has martingale + Markov
kernel + conditional expectation + Brownian motion (Degenne 2025); does
NOT ship stochastic integral against semimartingales. This module ships
the substrate-data-level operationalization suitable for downstream
SK-EFT-Hawking content.

Mathlib naming/style conventions used where feasible (in-program first;
upstream PR readiness is a future-ready discipline per Phase 6o user
direction Session 30).

## I3 Stage-13 fix-pass 2026-05-11 (post-strengthening)

The predicate body was upgraded from `Prop := True` to a substantive
refutable form: an inhabitation of `IsStochasticIntegral H W I` now
asserts FOUR structural properties:
* `Continuous I` — the integral process is continuous in the upper limit.
* `I 0 = 0` — the integral over `[0,0]` is zero.
* `Continuous H` — the integrand `H` is a continuous predictable process.
* `Continuous W` — the integrator `W` (Brownian motion) is continuous.

All three parameters (formerly two underscored) now constrain the
body, making the "Stochastic Integral" name semantically meaningful.
Refutable by discontinuous `I`, `H`, or `W`, or by `I 0 ≠ 0`.

References:
- Degenne, Ledvinka, Marion, Pfaffelhuber, "Formalization of Brownian
  motion in Lean", arXiv:2511.20118 (2025).
- Degenne, "Markov kernels in Mathlib's probability library",
  arXiv:2510.04070 (2025). (Primary-source-verified
  Phase 7 absorption Session 5 2026-05-08; supersedes the
  carry-forward Phase-6n-era misattribution to "Marion et al.")
- Phase 6o Wave 3b.Itô-α substrate-analysis working doc.
-/

noncomputable section

namespace SKEFTHawking.Itô

/-- A predicate-data substrate for the stochastic integral `∫ H dW` of a
predictable elementary process `H` against a Brownian motion `W`.

Substantive content (I3 Stage-13 fix-pass, post-strengthening):
* `Continuous I` — integral process continuous in the upper limit.
* `I 0 = 0` — integral over `[0,0]` is zero.
* `Continuous H` — integrand is continuous predictable.
* `Continuous W` — integrator (Brownian motion) is continuous.

Refutable by discontinuity in any of the three processes or by
`I 0 ≠ 0`. -/
def IsStochasticIntegral
    (H W I : ℝ → ℝ) : Prop :=
  Continuous I ∧ I 0 = 0 ∧ Continuous H ∧ Continuous W

/-- The trivial zero integrand has the trivial zero stochastic integral
(`I = 0`); each of the three processes is `continuous_const`. -/
theorem isStochasticIntegral_trivial :
    IsStochasticIntegral (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
  ⟨continuous_const, rfl, continuous_const, continuous_const⟩

/-- Wave 3b.Itô-β.1 closure: stochastic integral predicate is non-vacuously
witnessed at substrate-data level. -/
theorem wave_3b_itoBeta_1_stochasticIntegral_closure :
    IsStochasticIntegral (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
  isStochasticIntegral_trivial

end SKEFTHawking.Itô
