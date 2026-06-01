import Mathlib.Tactic
import SKEFTHawking.QuantumNetwork.Envelope

/-!
# Repeater-chain breadth: BDCZ nesting, usefulness threshold, QBER (Phase 6AB, Wave 4)

Builds on the Werner-iterated end-to-end fidelity (Phase 6AA `endToEndFidelity`):

- the **BDCZ nesting-doubling** identity (a length-`2m` chain = two length-`m`
  segments swapped — the doubling recursion of nested-purification repeaters);
- the **teleportation-usefulness threshold** `F_e2e > 1/2` (Horodecki: teleportation
  fidelity `> 2/3`), characterized exactly by the `k`-fold Werner parameter;
- the **end-to-end QBER** `1 − F_e2e` and its monotone growth with chain length,
  the secret-key-rate-relevant degradation.

We deliberately do NOT hardcode the BB84 binary-entropy positive-key crossover
(~11% QBER) — that constant is transcendental; the positive-key region is stated
as `QBER < q ↔ F_e2e > 1−q` with the threshold left as a parameter.

Invariants (Phase 6AB): kernel-pure, zero sorry, no project-local axioms,
no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

/-- **BDCZ nesting-doubling:** a length-`2m` swap chain equals two length-`m`
segments swapped — the doubling recursion underlying nested-purification repeaters. -/
theorem endToEndFidelity_nest_double (F : ℝ) (m : ℕ) :
    endToEndFidelity F (2 * m)
      = wernerSwapFidelity (endToEndFidelity F m) (endToEndFidelity F m) := by
  apply wernerParam_injective
  rw [wernerParam_swap, endToEndFidelity_param, endToEndFidelity_param, two_mul, pow_add]

/-- **Teleportation-usefulness threshold.** The end-to-end chain beats the classical
fidelity bound (`F_e2e > 1/2`, i.e. average teleportation fidelity `> 2/3`, Horodecki)
iff the `k`-fold Werner parameter exceeds `1/3`. -/
theorem endToEnd_teleportation_useful (F : ℝ) (k : ℕ) :
    1 / 2 < endToEndFidelity F k ↔ 1 / 3 < (wernerParam F) ^ k := by
  unfold endToEndFidelity
  constructor <;> intro h <;> linarith

/-- End-to-end quantum bit-error rate `1 − F_e2e`. -/
noncomputable def endToEndQBER (F : ℝ) (k : ℕ) : ℝ := 1 - endToEndFidelity F k

/-- QBER stays in `[0, 3/4]` over the physical per-link range. -/
theorem endToEndQBER_mem (F : ℝ) (k : ℕ) (hlo : 1 / 4 ≤ F) (hhi : F ≤ 1) :
    0 ≤ endToEndQBER F k ∧ endToEndQBER F k ≤ 3 / 4 := by
  obtain ⟨h1, h2⟩ := swapChain_fidelity_envelope F k hlo hhi
  unfold endToEndQBER
  constructor <;> linarith

/-- **QBER grows with chain length** (more hops ⇒ more error) — the secret-key-rate-
relevant degradation. Positive-key region: `QBER < q ↔ F_e2e > 1−q` (threshold `q`
left as a parameter; the BB84 entropy crossover is not hardcoded). -/
theorem endToEndQBER_monotone_length (F : ℝ) (hlo : 1 / 4 ≤ F) (hhi : F ≤ 1) {k k' : ℕ}
    (h : k ≤ k') : endToEndQBER F k ≤ endToEndQBER F k' := by
  have := endToEndFidelity_antitone_length F hlo hhi h
  unfold endToEndQBER
  linarith

end SKEFTHawking.QuantumNetwork
