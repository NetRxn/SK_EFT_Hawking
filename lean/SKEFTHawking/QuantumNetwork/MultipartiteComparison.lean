import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import SKEFTHawking.QuantumNetwork.WStateRate
import SKEFTHawking.QuantumNetwork.SecretKeyRate

/-!
# Multipartite random-party distillation: W₃ versus GHZ₃ (Phase 6AC, Wave 2)

Fortescue–Lo's comparison (PRA 78, 012348 (2008), Thm 3.5; exact-formulas DR §3):
*"Random distillation is always advantageous for W-class three-qubit states (but
only sometimes for GHZ-class states)."* Concretely:

* **GHZ₃** gains nothing from randomizing the target pair: its random-party rate
  equals its specified-pair rate, both `= 1`. We encode this as the **modeling
  input** `ghz3RandomizationAdvantage := 0` (cited, not a derived theorem).
* **W₃** gains strictly: the random-party finite-round yield `D/(D+1)`
  (`fortescueLoYield`, Phase 6AA) surpasses the specified-pair single-copy bound
  `2/3` for `D ≥ 3`, so its randomization advantage is strictly positive — strictly
  greater than GHZ₃'s zero advantage (`w3_beats_ghz_randomization_advantage`).
* The W₃ **asymptotic specified** rate is the entanglement of assistance
  `H₂(1/3) = log₂3 − 2/3 ≈ 0.9183` (Smolin–Verstraete–Winter; Fortescue–Lo), which
  is *strictly below* the random-party asymptotic rate `1`
  (`w3_asymptotic_specified_lt_one`, via Mathlib `binEntropy_lt_log_two`).
* The random-party finite-round yields **converge to `1`**, the GHZ₃ rate
  (`fortescueLoYield_tendsto_one`) — W₃'s random-party rate asymptotically matches
  GHZ₃'s. (The *optimality* of `1`, i.e. that no protocol beats it, is the open
  Fortescue–Lo conjecture and is NOT claimed here.)

Invariants (Phase 6AC): kernel-pure, zero sorry, no project-local axioms,
no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Real

/-- W₃ specified-pair single-copy distillation bound `2/3` (D'Hondt–Panangaden;
Fortescue–Lo PRL 98, 260501 (2007) abstract). -/
noncomputable def w3SpecifiedSingleCopyBound : ℝ := 2 / 3

/-- GHZ₃ random-party distillation rate. **Modeling input (cited, Fortescue–Lo PRA 78, 012348
(2008)):** GHZ₃ distills one EPR pair between any chosen pair of parties with certainty, so its
random-party rate is `1`. -/
noncomputable def ghz3RandomPartyRate : ℝ := 1

/-- GHZ₃ specified-pair distillation rate. **Modeling input (cited):** also `1` — GHZ₃ already
distills a specified pair with certainty, so randomizing the target pair gains nothing. -/
noncomputable def ghz3SpecifiedRate : ℝ := 1

/-- GHZ₃ randomization advantage, **derived** as `random-party rate − specified-pair rate` (the same
`(random − specified)` structure as `w3RandomizationAdvantage`), rather than hardcoded to its value. -/
noncomputable def ghz3RandomizationAdvantage : ℝ := ghz3RandomPartyRate - ghz3SpecifiedRate

/-- **GHZ₃'s randomization advantage is zero — DERIVED, not assumed.** Its random-party and
specified-pair rates are both `1` (the cited Fortescue–Lo modeling inputs), so their difference
vanishes. This replaces the former hardcoded `ghz3RandomizationAdvantage := 0`, making the
comparison `w3_beats_ghz_randomization_advantage` genuinely two-sided: the GHZ side is now a
consequence of the equal-rates model, not a definition tuned to the conclusion. -/
theorem ghz3RandomizationAdvantage_eq_zero : ghz3RandomizationAdvantage = 0 := by
  unfold ghz3RandomizationAdvantage ghz3RandomPartyRate ghz3SpecifiedRate; ring

/-- W₃ randomization advantage at `D` rounds: random-party finite-round yield minus
the specified-pair single-copy bound. -/
noncomputable def w3RandomizationAdvantage (D : ℕ) : ℝ :=
  fortescueLoYield D - w3SpecifiedSingleCopyBound

/-- **W₃ has a strictly positive randomization advantage for `D ≥ 3`** — randomizing
the target pair strictly helps, reducing to the shipped `fortescueLoYield_gt_two_thirds`. -/
theorem w3RandomizationAdvantage_pos {D : ℕ} (h : 3 ≤ D) :
    0 < w3RandomizationAdvantage D := by
  unfold w3RandomizationAdvantage w3SpecifiedSingleCopyBound
  have := fortescueLoYield_gt_two_thirds h
  linarith

/-- **W₃ strictly beats GHZ₃ in randomization advantage (Fortescue–Lo Thm 3.5).**
For `D ≥ 3` the W₃ random-party advantage is strictly greater than GHZ₃'s (zero):
random distillation helps W-class states but not GHZ-class states. -/
theorem w3_beats_ghz_randomization_advantage {D : ℕ} (h : 3 ≤ D) :
    ghz3RandomizationAdvantage < w3RandomizationAdvantage D := by
  rw [ghz3RandomizationAdvantage_eq_zero]
  exact w3RandomizationAdvantage_pos h

/-- W₃ asymptotic specified-pair rate: the entanglement of assistance
`H₂(1/3) = log₂3 − 2/3` in bits (Smolin–Verstraete–Winter PRA 72, 052317 (2005);
Fortescue–Lo). -/
noncomputable def w3AsymptoticSpecifiedRate : ℝ := binEntropyBit (1 / 3)

/-- **The W₃ asymptotic specified rate `H₂(1/3)` is strictly below `1`** — the
random-party asymptotic rate (and the GHZ₃ rate). Even asymptotically, randomizing
the target pair strictly helps W₃. Via Mathlib's `binEntropy_lt_log_two`. -/
theorem w3_asymptotic_specified_lt_one : w3AsymptoticSpecifiedRate < 1 := by
  unfold w3AsymptoticSpecifiedRate binEntropyBit
  rw [div_lt_one log_two_pos]
  exact (Real.binEntropy_lt_log_two).mpr (by norm_num)

/-- The W₃ asymptotic specified rate is strictly positive (`H₂(1/3) > 0`). -/
theorem w3_asymptotic_specified_pos : 0 < w3AsymptoticSpecifiedRate := by
  unfold w3AsymptoticSpecifiedRate binEntropyBit
  exact div_pos (Real.binEntropy_pos (by norm_num) (by norm_num)) log_two_pos

/-- **The W₃ random-party finite-round yields converge to `1`**, the GHZ₃ rate:
`D/(D+1) → 1`. So the W₃ random-party rate asymptotically matches GHZ₃'s. (Optimality
of `1` — that no protocol exceeds it — is the open Fortescue–Lo conjecture, NOT claimed.) -/
theorem fortescueLoYield_tendsto_one :
    Filter.Tendsto fortescueLoYield Filter.atTop (nhds 1) := by
  have h : ∀ D : ℕ, (1 : ℝ) - 1 / (D + 1) = fortescueLoYield D := by
    intro D
    unfold fortescueLoYield
    have : (D : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [show (1 : ℝ) = 1 - 0 by ring]
  exact Filter.Tendsto.congr h
    (tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat)

end SKEFTHawking.QuantumNetwork
