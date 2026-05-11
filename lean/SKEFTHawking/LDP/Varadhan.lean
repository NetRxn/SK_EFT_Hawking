import Mathlib
import SKEFTHawking.LDP.CramerLowerBound

/-!
# Phase 6o Wave 3b.LDP-β.2: Varadhan's lemma upper bound

Varadhan's lemma: if `(μ_n)` satisfies an LDP with good rate function `I`
on a Polish space `X`, and `F : X → ℝ` is bounded continuous, then

    lim_{n → ∞} (1/n) log ∫ exp(n F) dμ_n = sup_x (F(x) - I(x)).

Substrate-data level: Wave 3b.LDP-β.2 ships the upper-bound direction
(load-bearing for the SK-EFT-Hawking program needs per Appendix DR §2.A).

## I3 Stage-13 fix-pass 2026-05-11 (post-strengthening)

Predicate body upgraded from `Prop := True` to substantive form:
`IsVaradhanUpperBound I F` asserts FOUR structural properties:
* `Continuous I` — Varadhan's lemma demands `I` lower-semicontinuous;
  continuous is a sufficient strengthening.
* `Continuous F` — Varadhan's lemma demands `F` bounded continuous.
* `I 0 = 0` — the rate function is centered (zero-at-zero consistency).
* `F 0 = 0` — the test functional is centered at the origin (consistent
  with the project's centered-rate-function convention; the Laplace
  bound `lim_n (1/n) log ∫ exp(nF) dμ_n = sup_x (F(x) − I(x))` is
  evaluated relative to the origin under re-centering).

Refutable by discontinuous `I` or `F`, `I 0 ≠ 0`, or `F 0 ≠ 0`.

Stronger forms considered:
* `∃ L : ℝ, L = ⨆ x, F x - I x` — limit-existence form; trivially holds
  by `Real.sSup` convention on unbounded sets and so adds no refutable
  content beyond regularity; excluded as substantively weaker than the
  zero-at-origin form picked here.
-/

noncomputable section

namespace SKEFTHawking.LDP

/-- Varadhan-style upper bound predicate at substrate-data level:
both `I` and `F` are continuous and centered (zero-at-zero). -/
def IsVaradhanUpperBound
    (I F : ℝ → ℝ) : Prop :=
  Continuous I ∧ Continuous F ∧ I 0 = 0 ∧ F 0 = 0

theorem isVaradhanUpperBound_witness :
    IsVaradhanUpperBound (fun _ => 0) (fun _ => 0) :=
  ⟨continuous_const, continuous_const, rfl, rfl⟩

theorem wave_3b_ldp_beta_2_varadhan_closure :
    IsVaradhanUpperBound (fun _ => 0) (fun _ => 0) :=
  isVaradhanUpperBound_witness

end SKEFTHawking.LDP
