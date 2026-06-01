import Mathlib.Tactic
import SKEFTHawking.QuantumNetwork.Envelope
import SKEFTHawking.QuantumNetwork.Channels

/-!
# Decay-inclusive end-to-end fidelity envelope (Phase 6AB, Wave 2 — FLAGSHIP)

The realistic-network generalization of the Phase-6AA `swapChain_fidelity_envelope`:
each Werner link is degraded by memory decoherence during storage before the swap
chain. In the SeQUeNCe depolarizing model (DR-SIM §5b) a Werner state of fidelity
`F` stored for time `t` with coherence time `τ` degrades to

`F(t) = F·e^(−2t/τ) + (1 − e^(−2t/τ))/4`,

which — cleanly — **multiplies the Werner parameter by `e^(−2t/τ)`**. The
decay-inclusive end-to-end envelope then follows by composing this with the shipped
swap-chain envelope, still entirely in the real-parameter representation (no
density matrices / traceNorm).

Invariants (Phase 6AB): kernel-pure, zero sorry, no project-local axioms,
no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

/-- Memory-degraded Werner fidelity after storage time `t`, coherence time `τ`
(SeQUeNCe depolarizing form). -/
noncomputable def memoryDegradedFidelity (F t τ : ℝ) : ℝ :=
  F * Real.exp (-2 * t / τ) + (1 - Real.exp (-2 * t / τ)) / 4

/-- Memory decoherence multiplies the Werner parameter by `e^(−2t/τ)`. -/
theorem memoryDegraded_wernerParam (F t τ : ℝ) :
    wernerParam (memoryDegradedFidelity F t τ) = Real.exp (-2 * t / τ) * wernerParam F := by
  unfold wernerParam memoryDegradedFidelity; ring

/-- Degraded fidelity stays physical: `F ∈ [1/4,1]`, `t ≥ 0`, `τ > 0` ⟹ `F(t) ∈ [1/4,1]`. -/
theorem memoryDegradedFidelity_mem {F t τ : ℝ} (hlo : 1 / 4 ≤ F) (hhi : F ≤ 1)
    (ht : 0 ≤ t) (hτ : 0 < τ) :
    1 / 4 ≤ memoryDegradedFidelity F t τ ∧ memoryDegradedFidelity F t τ ≤ 1 := by
  have hc0 : (0 : ℝ) < Real.exp (-2 * t / τ) := Real.exp_pos _
  have hc1 : Real.exp (-2 * t / τ) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hτ)
  unfold memoryDegradedFidelity
  refine ⟨?_, ?_⟩
  · nlinarith [mul_nonneg (le_of_lt hc0) (show (0 : ℝ) ≤ F - 1 / 4 by linarith)]
  · nlinarith [mul_nonneg (le_of_lt hc0) (show (0 : ℝ) ≤ 1 - F by linarith), hc1]

/-- **FLAGSHIP — decay-inclusive end-to-end fidelity envelope.** For a `k`-swap chain
of Werner links each with per-link fidelity `F ∈ [1/4,1]` stored for time `t ≥ 0`
with coherence `τ > 0`, the end-to-end fidelity provably lies in `[1/4,1]`. The
realistic-network generalization of `swapChain_fidelity_envelope`. -/
theorem decayInclusive_fidelity_envelope {F t τ : ℝ} (k : ℕ)
    (hlo : 1 / 4 ≤ F) (hhi : F ≤ 1) (ht : 0 ≤ t) (hτ : 0 < τ) :
    1 / 4 ≤ endToEndFidelity (memoryDegradedFidelity F t τ) k ∧
      endToEndFidelity (memoryDegradedFidelity F t τ) k ≤ 1 := by
  obtain ⟨h1, h2⟩ := memoryDegradedFidelity_mem hlo hhi ht hτ
  exact swapChain_fidelity_envelope (memoryDegradedFidelity F t τ) k h1 h2

/-- Degraded fidelity is antitone in storage time (more storage ⇒ lower fidelity). -/
theorem memoryDegradedFidelity_antitone_time {F τ : ℝ} (hlo : 1 / 4 ≤ F) (hτ : 0 < τ)
    {t t' : ℝ} (htt : t ≤ t') :
    memoryDegradedFidelity F t' τ ≤ memoryDegradedFidelity F t τ := by
  have hc : Real.exp (-2 * t' / τ) ≤ Real.exp (-2 * t / τ) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_div_iff₀ hτ hτ]
    nlinarith [mul_nonneg (le_of_lt hτ) (sub_nonneg.mpr htt)]
  unfold memoryDegradedFidelity
  nlinarith [hc, mul_nonneg (sub_nonneg.mpr hc) (show (0 : ℝ) ≤ F - 1 / 4 by linarith)]

/-- Decay-inclusive end-to-end fidelity is antitone in storage time. -/
theorem decayInclusive_antitone_time {F τ : ℝ} (k : ℕ) (hlo : 1 / 4 ≤ F) (hhi : F ≤ 1)
    (hτ : 0 < τ) {t t' : ℝ} (ht : 0 ≤ t) (htt : t ≤ t') :
    endToEndFidelity (memoryDegradedFidelity F t' τ) k ≤
      endToEndFidelity (memoryDegradedFidelity F t τ) k := by
  have ht' : 0 ≤ t' := le_trans ht htt
  obtain ⟨hlo', _⟩ := memoryDegradedFidelity_mem hlo hhi ht' hτ
  exact endToEndFidelity_mono_fidelity k hlo' (memoryDegradedFidelity_antitone_time hlo hτ htt)
end SKEFTHawking.QuantumNetwork
