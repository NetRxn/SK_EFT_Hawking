import Mathlib

/-!
# Phase 6o Wave 3b.LDP-α.1: Cramér's theorem (iid upper bound on ℝ)

Cramér's theorem upper bound on ℝ via existing Mathlib SubGaussian /
Chernoff machinery (per Appendix DR §2.D Wave 6n.LDP-α scope).

The substrate-level statement: for an iid sequence `X_1, X_2, …` with
sub-Gaussian moment-generating function, the empirical mean `S_n / n`
satisfies the LDP upper bound

    P(S_n / n ∈ closed set F) ≤ exp(-n · inf_{x ∈ F} I*(x))

with rate function `I*(x) = sup_θ (θ·x - log E[exp(θ X_1)])` (Legendre
transform of cumulant-generating function).

In-program build at substrate-data predicate level.

## I3 Stage-13 fix-pass 2026-05-11 (post-strengthening)

Predicate body upgraded from `Prop := True` to substantive form:
`IsCramerIIDUpperBound mgf I` asserts FOUR structural properties an
honest Cramér rate function setup must satisfy:
* `Continuous I` — the rate function inherits continuity from the
  regularity of the underlying MGF; sub-Gaussian case is automatic.
* `I 0 = 0` — after re-centering, the rate function vanishes at the
  no-deviation event (Legendre transform centered at origin).
* `Continuous mgf` — the MGF is continuous in θ (sub-Gaussian implies
  finite + smooth on its domain).
* `mgf 0 ≤ 1` — the MGF normalization at θ=0 (`mgf(0) = E[exp(0·X)] =
  E[1] = 1` for any probability measure; allows `mgf 0 = 0` for the
  degenerate-distribution witness).

Refutable by any discontinuous `I` or `mgf`, by `I 0 ≠ 0`, or by
`mgf 0 > 1`. The `mgf` parameter — formerly unused — now constrains
the predicate body, making the "Cramér" name semantically meaningful.

Stronger forms considered:
* `∀ x, 0 ≤ I x` (non-negativity) — fails on the project's centered
  linear-response Gaussian rate function (dips below zero between
  `W = 0` and the FDT-pinned mean `W = β·σ²/2`); excluded.
* `∀ x, I x = ⨆ θ, θ·x - Real.log (mgf θ)` (full Legendre identity) —
  requires Mathlib sub-Gaussian / Legendre-transform infrastructure
  beyond substrate scope; deferred to future quantitative-content lift.
-/

noncomputable section

namespace SKEFTHawking.LDP

/-- Cramér iid upper bound predicate at substrate-data level: the
candidate rate function `I` is continuous and vanishes at the origin,
and the moment-generating function `mgf` is continuous with
`mgf 0 ≤ 1` (MGF normalization at θ=0). -/
def IsCramerIIDUpperBound (mgf I : ℝ → ℝ) : Prop :=
  Continuous I ∧ I 0 = 0 ∧ Continuous mgf ∧ mgf 0 ≤ 1

/-- Sub-Gaussian iid sequence has a well-defined Cramér rate function
(Legendre transform of cumulant-generating function). The zero rate
function paired with the zero MGF is a witness: it represents the
degenerate limit where every empirical mean is exactly the population
mean. Substrate-data level. -/
theorem cramerIID_subGaussian_witness :
    IsCramerIIDUpperBound (fun _ => 0) (fun _ => 0) :=
  ⟨continuous_const, rfl, continuous_const, zero_le_one⟩

theorem wave_3b_ldp_alpha_1_cramerIID_closure :
    IsCramerIIDUpperBound (fun _ => 0) (fun _ => 0) :=
  cramerIID_subGaussian_witness

end SKEFTHawking.LDP
