import SKEFTHawking.LandauerConductance

/-!
# Certified conductance quantization (Phase 6BA, Wave 3)

The falsifiable, certificate-grade transport result built on the Wave-2 Landauer
conductance: in the zero-temperature linear-response limit the conductance of an
`n`-channel conductor is `G = G₀ · ∑ τ_i` (the sum of the per-eigenchannel transmissions
`τ_i ∈ [0,1]`), so it is **bounded by `n·G₀`** and **quantized at `n·G₀`** when every
channel is fully open. The certificate is the bound + its falsifier:

    G ≤ n·G₀ ,    (∀ i, τ_i = 1) → G = n·G₀ ,    G > n·G₀ → False .

This is the conductance-quantization theorem of the quantum point contact (van Wees /
Wharam 1988), here machine-checked as a one-sided certificate: a measured conductance
exceeding `n·G₀` is impossible for `n` channels, because it would require some channel to
transmit with probability `> 1`.

## References

- van Wees et al., PRL 60, 848 (1988) — quantized conductance of a point contact.
- Wharam et al., J. Phys. C 21, L209 (1988) — one-dimensional transport quantization.
- Datta, *Electronic Transport in Mesoscopic Systems* (CUP 1995), §2.5.

Invariants (Phase 6BA): kernel-pure `{propext, Classical.choice, Quot.sound}`; zero sorry;
no project-local axioms; no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.NEGF

open scoped BigOperators

/-- Zero-temperature Landauer conductance of an `n`-channel conductor with per-eigenchannel
transmissions `τ : Fin n → ℝ`: `G = G₀ · ∑ τ_i` (`G₀ = 2e²/h` the conductance quantum). -/
noncomputable def channelConductance (G₀ : ℝ) {n : ℕ} (τ : Fin n → ℝ) : ℝ :=
  G₀ * ∑ i, τ i

/-- **Certificate bound `G ≤ n·G₀`** — every channel transmits with probability `≤ 1`, so the
total conductance cannot exceed `n` conductance quanta. -/
theorem channelConductance_le_quantum (G₀ : ℝ) (hG₀ : 0 ≤ G₀) {n : ℕ} (τ : Fin n → ℝ)
    (hτ : ∀ i, τ i ≤ 1) : channelConductance G₀ τ ≤ n * G₀ := by
  unfold channelConductance
  have hsum : ∑ i, τ i ≤ (n : ℝ) := by
    calc ∑ i, τ i ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hτ i)
      _ = (n : ℝ) := by simp
  calc G₀ * ∑ i, τ i ≤ G₀ * (n : ℝ) := mul_le_mul_of_nonneg_left hsum hG₀
    _ = (n : ℝ) * G₀ := by ring

/-- **Conductance quantization `G = n·G₀`** — when every one of the `n` channels is fully open
(`τ_i = 1`), the conductance is exactly `n` conductance quanta. -/
theorem conductance_quantization (G₀ : ℝ) {n : ℕ} (τ : Fin n → ℝ) (hτ : ∀ i, τ i = 1) :
    channelConductance G₀ τ = (n : ℝ) * G₀ := by
  unfold channelConductance
  simp only [hτ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- **The falsifier `G > n·G₀ → ⊥`** — a conductance strictly exceeding `n·G₀` is impossible for
`n` channels (it would force some `τ_i > 1`). The certificate's contrapositive. -/
theorem conductance_quantization_falsifier (G₀ : ℝ) (hG₀ : 0 ≤ G₀) {n : ℕ} (τ : Fin n → ℝ)
    (hτ : ∀ i, τ i ≤ 1) (hexceed : (n : ℝ) * G₀ < channelConductance G₀ τ) : False :=
  absurd (channelConductance_le_quantum G₀ hG₀ τ hτ) (not_le.mpr hexceed)

/-- **Concrete `norm_num`-backed falsifier instance** — a two-channel quantum point contact
cannot carry three conductance quanta (`G = 3·G₀` with `G₀ > 0`): it would require total
transmission `3 > 2`. -/
theorem two_channel_no_three_quanta (G₀ : ℝ) (hG₀ : 0 < G₀) (τ : Fin 2 → ℝ)
    (hτ : ∀ i, τ i ≤ 1) (h : channelConductance G₀ τ = 3 * G₀) : False := by
  have hle := channelConductance_le_quantum G₀ hG₀.le τ hτ
  rw [h] at hle
  norm_num at hle
  nlinarith [hG₀]

/-- **Bridge to the Wave-2 Landauer integral** — the `n`-channel zero-temperature conductance is
the linear-response limit (`landauerConductance`) of an energy-independent transmission equal to
the total transmission `∑ τ_i`, given the Fermi-window normalization. Grounds the channel
certificate in the full conductance functional. -/
theorem channelConductance_eq_landauer (G₀ μ β : ℝ) {n : ℕ} (τ : Fin n → ℝ)
    (hw : ∫ E, fermiWindow μ β E = 1) :
    channelConductance G₀ τ = landauerConductance G₀ (fun _ => ∑ i, τ i) μ β := by
  rw [landauerConductance_const_transmission G₀ (∑ i, τ i) μ β hw, channelConductance]

end SKEFTHawking.NEGF
