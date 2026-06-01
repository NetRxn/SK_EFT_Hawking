import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Normed
import SKEFTHawking.QuantumNetwork.Basic

/-!
# W1′ Tier-1 anchors: linear-optics BSM bound + physics-only link rate (Phase 6AD / Bucket 3.2)

The two model-independent Tier-1 anchors deferred from Phase 6AA (DR-SIM §6): both are
clean, simulator-independent facts a network operator cares about.

## Linear-optics Bell-state-measurement success bound

Calsamiglia & Lütkenhaus (Appl. Phys. B 72, 67–71 (2001)): a linear-optics Bell-state
analyzer can conclusively identify at most **2 of the 4** Bell states, so its success
probability cannot exceed `1/2`. We model a BSM that resolves `d` of the 4 outcomes
(uniform prior) as success probability `d/4`; the Calsamiglia–Lütkenhaus bound `d ≤ 2`
then forces `≤ 1/2` (`bsmSuccessProb_le_half_of_linearOptics`), versus the complete
deterministic 4-outcome BSM at `1` (`bsmSuccessProb_complete`) — the one the Werner-swap
composition (Phase 6AA `wernerSwapFidelity`) assumes.

## Physics-only elementary-link rate

The model-independent elementary-link entanglement-generation time is the geometric
expectation `τ = L/(c·p_link)`: one-way latency `L/c` times the expected number of
heralded attempts `1/p_link`. The expected-attempts factor is *derived* here as the mean
of the geometric distribution (`geometric_expected_attempts`, a `HasSum`), not asserted.
This is Tier-1 (physics); the *handshake-inclusive* link time (the 4.16–4.33× simulator
split) is Tier-3 and deliberately not bounded.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

/-! ### Linear-optics BSM success bound -/

/-- Success probability of a BSM resolving `d` of the 4 Bell outcomes (uniform prior). -/
noncomputable def bsmSuccessProb (d : ℕ) : ℝ := d / 4

/-- **Calsamiglia–Lütkenhaus linear-optics bound.** A linear-optics Bell-state analyzer
resolves at most `2` of the `4` Bell states (`d ≤ 2`), hence succeeds with probability
`≤ 1/2`. -/
theorem bsmSuccessProb_le_half_of_linearOptics {d : ℕ} (h : d ≤ 2) :
    bsmSuccessProb d ≤ 1 / 2 := by
  have hd : (d : ℝ) ≤ 2 := by exact_mod_cast h
  unfold bsmSuccessProb; linarith

/-- The linear-optics maximum `2/4 = 1/2` is achieved (two resolvable Bell outcomes). -/
@[simp] theorem bsmSuccessProb_linearOptics_max : bsmSuccessProb 2 = 1 / 2 := by
  unfold bsmSuccessProb; norm_num

/-- A complete (deterministic 4-outcome) BSM succeeds with probability `1` — the
contrast that the Werner-swap composition assumes. -/
@[simp] theorem bsmSuccessProb_complete : bsmSuccessProb 4 = 1 := by
  unfold bsmSuccessProb; norm_num

/-- More resolvable outcomes ⇒ higher success probability. -/
theorem bsmSuccessProb_mono : Monotone bsmSuccessProb := by
  intro a b h
  unfold bsmSuccessProb
  gcongr

/-! ### Physics-only elementary-link rate -/

/-- **Expected number of heralded attempts is `1/p`** — the mean of the geometric
distribution with per-attempt success `p`, derived from the geometric series
`∑ (n+1)·p·(1−p)^n = 1/p`. -/
theorem geometric_expected_attempts {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * p * (1 - p) ^ n) (1 / p) := by
  have hr : ‖(1 - p : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
  have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one hr).mul_left p
  have h2 := (hasSum_geometric_of_norm_lt_one hr).mul_left p
  have hsum := h1.add h2
  have hfun : (fun n : ℕ => ((n : ℝ) + 1) * p * (1 - p) ^ n)
      = (fun b : ℕ => p * ((b : ℝ) * (1 - p) ^ b) + p * (1 - p) ^ b) := by
    funext n; ring
  have hval : p * ((1 - p) / (1 - (1 - p)) ^ 2) + p * (1 - (1 - p))⁻¹ = 1 / p := by
    have hp' : p ≠ 0 := ne_of_gt hp0
    rw [show (1 : ℝ) - (1 - p) = p by ring]
    field_simp; ring
  rw [hfun, ← hval]
  exact hsum

/-- Physics-only elementary-link entanglement-generation time `τ = L/(c·p_link)`. -/
noncomputable def linkRate (L c p : ℝ) : ℝ := L / (c * p)

/-- **The link rate is one-way latency times expected attempts**: `τ = (L/c)·(1/p)`. -/
theorem linkRate_eq_latency_mul_attempts (L : ℝ) {c p : ℝ} (hc : c ≠ 0) (hp : p ≠ 0) :
    linkRate L c p = (L / c) * (1 / p) := by
  unfold linkRate; field_simp

/-- The link time is positive for physical parameters. -/
theorem linkRate_pos {L c p : ℝ} (hL : 0 < L) (hc : 0 < c) (hp : 0 < p) :
    0 < linkRate L c p := by
  unfold linkRate; positivity

/-- **Lower per-attempt success ⇒ strictly longer expected link time** (antitone in
`p_link`) — the physically meaningful loss dependence. -/
theorem linkRate_antitone_success {L c : ℝ} (hL : 0 ≤ L) (hc : 0 < c) {p p' : ℝ}
    (hp : 0 < p) (hpp : p ≤ p') : linkRate L c p' ≤ linkRate L c p := by
  unfold linkRate
  gcongr

/-- **Longer elementary link ⇒ longer expected time** (monotone in `L`). -/
theorem linkRate_monotone_length {c p : ℝ} (hc : 0 < c) (hp : 0 < p) {L L' : ℝ}
    (hLL : L ≤ L') : linkRate L c p ≤ linkRate L' c p := by
  unfold linkRate
  gcongr

end SKEFTHawking.QuantumNetwork
