import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import SKEFTHawking.QuantumNetwork.RepeaterChain

/-!
# BB84 secret-key rate over a repeater chain (Phase 6AC, Wave 1)

The Shor–Preskill asymptotic secret-key rate of BB84 against the depolarizing
(symmetric) channel (Shor & Preskill, Phys. Rev. Lett. 85, 441 (2000)) is
`r(e) = 1 − 2·h₂(e)`, where `h₂` is the **base-2** binary
entropy and `e` is the quantum bit-error rate (QBER). Mathlib's `Real.binEntropy`
is in *nats* (natural log), so the bits version is `h₂(p) = binEntropy p / log 2`;
in this normalization `h₂(1/2) = 1` and the perfect channel gives `r(0) = 1`.

The protocol-level point of this wave is that the **positive-key crossover is
proven, not hardcoded.** We do *not* write the customary `e* ≈ 0.11`. Instead:

* `bb84KeyRate_pos_iff_binEntropy_lt`: `0 < r(e) ↔ binEntropy e < log 2 / 2` — the
  crossover stated as the entropy condition `h₂(e) < 1/2`;
* `bb84KeyRate_strictAntiOn`: the rate strictly decreases in the error rate on
  `[0, 1/2]` (more channel noise ⇒ less key);
* `bb84_crossover_exists`: a genuine crossover `e* ∈ (0, 1/2)` with `r(e*) = 0`
  exists (intermediate-value theorem on the continuous rate), and
* `bb84KeyRate_pos_iff_lt_crossover`: for any such crossover `e*`, positivity is
  exactly `e < e*` — the "positive iff below threshold" characterization, with the
  decimal value of `e*` left implicit (it is the root of `h₂(e) = 1/2`).

Finally `bb84_positiveKey_fidelity_threshold` composes this with the Phase-6AB
end-to-end QBER (`endToEndQBER = 1 − F_e2e`): a `k`-swap Werner chain yields a
positive secret key iff its end-to-end fidelity exceeds the crossover fidelity
`1 − e*`.

This is the key-rate *formula* and its analysis, not a from-scratch security
proof. Invariants (Phase 6AC): kernel-pure, zero sorry, no project-local axioms,
no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Real

/-- Base-2 (bits) binary entropy: Mathlib's nats `binEntropy` renormalized by
`log 2`. `binEntropyBit (1/2) = 1`. -/
noncomputable def binEntropyBit (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

/-- `log 2 > 0` — the renormalization constant is positive. -/
theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- The bits normalization: `h₂(1/2) = 1`. -/
@[simp] theorem binEntropyBit_two_inv : binEntropyBit 2⁻¹ = 1 := by
  unfold binEntropyBit
  rw [Real.binEntropy_two_inv, div_self log_two_pos.ne']

/-- **Shor–Preskill BB84 asymptotic secret-key rate** `r(e) = 1 − 2·h₂(e)`. -/
noncomputable def bb84KeyRate (e : ℝ) : ℝ := 1 - 2 * binEntropyBit e

/-- Perfect channel: a noiseless BB84 link yields one secret bit per sifted bit. -/
@[simp] theorem bb84KeyRate_zero : bb84KeyRate 0 = 1 := by
  simp [bb84KeyRate, binEntropyBit]

/-- At the fully-symmetric error rate the rate is `1 − 2 = −1` (no key). -/
@[simp] theorem bb84KeyRate_two_inv : bb84KeyRate 2⁻¹ = -1 := by
  rw [bb84KeyRate, binEntropyBit_two_inv]; norm_num

/-- **Positive-key crossover (entropy form).** The key rate is positive exactly
when the (nats) entropy is below `log 2 / 2`, i.e. `h₂(e) < 1/2`. No decimal
crossover constant is hardcoded. -/
theorem bb84KeyRate_pos_iff_binEntropy_lt (e : ℝ) :
    0 < bb84KeyRate e ↔ Real.binEntropy e < Real.log 2 / 2 := by
  unfold bb84KeyRate binEntropyBit
  rw [sub_pos, show (2:ℝ) * (Real.binEntropy e / Real.log 2)
      = Real.binEntropy e / (Real.log 2 / 2) by ring,
    div_lt_one (by have := log_two_pos; linarith)]

/-- **The secret-key rate strictly decreases in the error rate** on `[0, 1/2]`:
more channel noise yields strictly less key. -/
theorem bb84KeyRate_strictAntiOn : StrictAntiOn bb84KeyRate (Set.Icc 0 2⁻¹) := by
  intro a ha b hb hab
  have hmono := Real.binEntropy_strictMonoOn ha hb hab
  unfold bb84KeyRate binEntropyBit
  have hdiv : Real.binEntropy a / Real.log 2 < Real.binEntropy b / Real.log 2 :=
    (div_lt_div_iff_of_pos_right log_two_pos).mpr hmono
  linarith

/-- `bb84KeyRate` is continuous (composition of `binEntropy` with affine maps). -/
theorem bb84KeyRate_continuous : Continuous bb84KeyRate := by
  unfold bb84KeyRate binEntropyBit
  fun_prop

/-- **A genuine positive-key crossover exists.** There is an error rate
`e* ∈ (0, 1/2)` at which the rate vanishes — the root of `h₂(e) = 1/2`. Its
decimal value (`≈ 0.11`) is never asserted; only its existence (via the
intermediate-value theorem on the continuous, strictly decreasing rate). -/
theorem bb84_crossover_exists :
    ∃ e ∈ Set.Ioo (0 : ℝ) 2⁻¹, bb84KeyRate e = 0 := by
  have hle : (0 : ℝ) ≤ 2⁻¹ := by norm_num
  have hcont : ContinuousOn bb84KeyRate (Set.Icc 0 2⁻¹) :=
    bb84KeyRate_continuous.continuousOn
  have hmem : (0 : ℝ) ∈ Set.Icc (bb84KeyRate 2⁻¹) (bb84KeyRate 0) := by
    rw [bb84KeyRate_zero, bb84KeyRate_two_inv]; constructor <;> norm_num
  obtain ⟨e, he, hee⟩ := intermediate_value_Icc' hle hcont hmem
  refine ⟨e, ⟨?_, ?_⟩, hee⟩
  · rcases he.1.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, bb84KeyRate_zero] at hee; norm_num at hee
  · rcases he.2.lt_or_eq with h | h
    · exact h
    · exfalso; rw [h, bb84KeyRate_two_inv] at hee; norm_num at hee

/-- **Positive key iff below the crossover.** For *any* crossover `e*` (a zero of
the rate in `[0, 1/2]`), the rate is positive exactly for error rates below it.
This is the threshold characterization with the crossover's decimal value left
implicit; combined with `bb84_crossover_exists` (existence) and
`bb84KeyRate_strictAntiOn` (uniqueness on `[0,1/2]`) it pins the crossover. -/
theorem bb84KeyRate_pos_iff_lt_crossover {e eStar : ℝ}
    (he : e ∈ Set.Icc (0 : ℝ) 2⁻¹) (hes : eStar ∈ Set.Icc (0 : ℝ) 2⁻¹)
    (hStar : bb84KeyRate eStar = 0) : 0 < bb84KeyRate e ↔ e < eStar := by
  constructor
  · intro hpos
    rcases lt_trichotomy e eStar with h | h | h
    · exact h
    · rw [h, hStar] at hpos; exact absurd hpos (lt_irrefl 0)
    · have := bb84KeyRate_strictAntiOn hes he h
      rw [hStar] at this; linarith
  · intro hlt
    have := bb84KeyRate_strictAntiOn he hes hlt
    rw [hStar] at this; exact this

/-- **Positive-key fidelity threshold over the repeater chain.** With end-to-end
fidelity in the useful half `[1/2, 1]` (so the QBER lies in `[0, 1/2]`), a `k`-swap
Werner chain produces a positive BB84 secret key iff its end-to-end fidelity
exceeds the crossover fidelity `1 − e*`. Composes the Phase-6AB `endToEndQBER`
with the crossover above. -/
theorem bb84_positiveKey_fidelity_threshold {F eStar : ℝ} (k : ℕ)
    (hlo : 1 / 4 ≤ F) (hhi : F ≤ 1) (hF : 1 / 2 ≤ endToEndFidelity F k)
    (hes : eStar ∈ Set.Icc (0 : ℝ) 2⁻¹) (hStar : bb84KeyRate eStar = 0) :
    0 < bb84KeyRate (endToEndQBER F k) ↔ 1 - eStar < endToEndFidelity F k := by
  have hq : endToEndQBER F k ∈ Set.Icc (0 : ℝ) 2⁻¹ := by
    obtain ⟨hq0, _⟩ := endToEndQBER_mem F k hlo hhi
    refine ⟨hq0, ?_⟩
    unfold endToEndQBER; norm_num; linarith
  rw [bb84KeyRate_pos_iff_lt_crossover hq hes hStar]
  unfold endToEndQBER
  constructor <;> intro h <;> linarith

end SKEFTHawking.QuantumNetwork
