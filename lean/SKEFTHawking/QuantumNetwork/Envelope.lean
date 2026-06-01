import Mathlib.Tactic
import SKEFTHawking.QuantumNetwork.EndToEnd

/-!
# Fidelity envelope for the swap-chain reference scenario (Phase 6AA, Wave 5)

The capstone of the model-independent FIDELITY envelope: for the reference
scenario of a chain of `k` entanglement swaps of Werner links with per-link
fidelity `F ∈ [1/4, 1]`, the end-to-end fidelity provably lies in a certified
interval. It is a verified envelope: **any computed end-to-end fidelity outside it
is provably inconsistent with the Werner-swap-chain model**, and it is
model-independent (fidelity, not the connection-model-dependent generation time).

Invariants (Phase 6AA): kernel-pure, zero sorry, no project-local axioms,
no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

/-- For physical per-link fidelity `F ∈ [1/4, 1]`, the Werner parameter lies in `[0,1]`. -/
theorem wernerParam_mem_Icc {F : ℝ} (hlo : 1 / 4 ≤ F) (hhi : F ≤ 1) :
    0 ≤ wernerParam F ∧ wernerParam F ≤ 1 := by
  unfold wernerParam; constructor <;> linarith

/-- **W5 capstone — swap-chain fidelity envelope.** For a chain of `k` entanglement
swaps of Werner links each with per-link fidelity `F ∈ [1/4, 1]`, the end-to-end
fidelity provably lies in `[1/4, 1]`. Model-independent: any computed end-to-end
fidelity outside this interval is provably inconsistent with the model. -/
theorem swapChain_fidelity_envelope (F : ℝ) (k : ℕ) (hlo : 1 / 4 ≤ F) (hhi : F ≤ 1) :
    1 / 4 ≤ endToEndFidelity F k ∧ endToEndFidelity F k ≤ 1 := by
  obtain ⟨hw0, hw1⟩ := wernerParam_mem_Icc hlo hhi
  have hpk0 : 0 ≤ (wernerParam F) ^ k := pow_nonneg hw0 k
  have hpk1 : (wernerParam F) ^ k ≤ 1 := pow_le_one₀ hw0 hw1
  unfold endToEndFidelity
  constructor <;> linarith

/-- Envelope is monotone in per-link fidelity: better links ⇒ no-worse end-to-end. -/
theorem endToEndFidelity_mono_fidelity {F F' : ℝ} (k : ℕ) (hlo : 1 / 4 ≤ F) (h : F ≤ F') :
    endToEndFidelity F k ≤ endToEndFidelity F' k := by
  have hw0 : 0 ≤ wernerParam F := by unfold wernerParam; linarith
  have hww : wernerParam F ≤ wernerParam F' := by unfold wernerParam; linarith
  have hpow : (wernerParam F) ^ k ≤ (wernerParam F') ^ k := pow_le_pow_left₀ hw0 hww k
  unfold endToEndFidelity; linarith

/-- Longer chains transmit no more: end-to-end fidelity is antitone in chain length. -/
theorem endToEndFidelity_antitone_length (F : ℝ) (hlo : 1 / 4 ≤ F) (hhi : F ≤ 1) {k k' : ℕ}
    (h : k ≤ k') : endToEndFidelity F k' ≤ endToEndFidelity F k := by
  obtain ⟨hw0, hw1⟩ := wernerParam_mem_Icc hlo hhi
  have hpow : (wernerParam F) ^ k' ≤ (wernerParam F) ^ k := pow_le_pow_of_le_one hw0 hw1 h
  unfold endToEndFidelity; linarith

end SKEFTHawking.QuantumNetwork
