import SKEFTHawking.GrapheneNoiseFormula
import SKEFTHawking.CrooksAnalogHawking.LDPLinearResponse

/-!
# FDT-bound amplifier / detector noise floor (Phase 6AN, Wave 4)

A certificate-grade, kernel-pure noise floor for a linear amplifier / detector operating point,
assembled from the shipped fluctuation-dissipation substrate:

* **FDT (Johnson–Nyquist) floor** — `fdt_noise_floor_bound`: taking the Callen–Welton FDT lower bound
  `S_JN ≤ S_total` (with `S_JN = 4 kB_T σ_Q`, `GrapheneNoiseFormula.johnsonNyquistPSD`), the measured
  current-noise PSD of a linear device at finite positive temperature/conductance is strictly
  positive — it can never be noiseless. The floor rises monotonically with temperature
  (`johnsonNyquistPSD_mono_temp`) and conductance (`johnsonNyquistPSD_mono_conductance`).
* **Worked operating points** — `fdt_noise_floor_detector` (thermal floor + Hawking excess, strict)
  and `fdt_noise_floor_amplifier` (Caves quantum-limited added noise `≥ ℏω/2`).
* **Rare-event tail (LDP) companion** — `fdt_rare_event_tail`: the linear-response large-deviation
  rate function `linearResponseRateFunction β σ² W = (W − βσ²/2)²/(2σ²)` is *strictly positive* for
  every noise current `W` away from the FDT-pinned mean `βσ²/2` (`fdt_noise_current_mean`), so all
  large fluctuations are exponentially suppressed `P(W) ∼ e^{−N·I(W)}`. The forward/reverse tail
  asymmetry is the Gallavotti–Cohen / W-form fluctuation theorem `fdt_gallavotti_cohen`
  (`I(W) − I(−W) = −β W`, entropy production).

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open SKEFTHawking.GrapheneNoiseFormula SKEFTHawking.CrooksAnalogHawking

/-! ## FDT (Johnson–Nyquist) noise floor and operating-point monotonicity -/

/-- The Johnson–Nyquist (FDT) floor `4 kB_T σ_Q` rises with temperature. -/
theorem johnsonNyquistPSD_mono_temp {kB_T₁ kB_T₂ sigma_Q : ℝ} (hσ : 0 ≤ sigma_Q)
    (hT : kB_T₁ ≤ kB_T₂) : johnsonNyquistPSD kB_T₁ sigma_Q ≤ johnsonNyquistPSD kB_T₂ sigma_Q := by
  unfold johnsonNyquistPSD; nlinarith [mul_nonneg (sub_nonneg.mpr hT) hσ]

/-- The Johnson–Nyquist (FDT) floor `4 kB_T σ_Q` rises with conductance. -/
theorem johnsonNyquistPSD_mono_conductance {kB_T sigma_Q₁ sigma_Q₂ : ℝ} (hT : 0 ≤ kB_T)
    (hσ : sigma_Q₁ ≤ sigma_Q₂) :
    johnsonNyquistPSD kB_T sigma_Q₁ ≤ johnsonNyquistPSD kB_T sigma_Q₂ := by
  unfold johnsonNyquistPSD; nlinarith [mul_nonneg hT (sub_nonneg.mpr hσ)]

/-- **FDT (Johnson–Nyquist) noise floor.** Take the Callen–Welton fluctuation–dissipation theorem as
the physical input: the measured current-noise PSD `S_total` of a linear device at operating point
`(kB_T, σ_Q)` is bounded below by the thermal floor `S_JN = 4 kB_T σ_Q ≤ S_total`. Then at any finite
positive temperature and conductance the floor is strictly positive and hence so is the total: a
linear detector/amplifier can never be noiseless. -/
theorem fdt_noise_floor_bound {kB_T sigma_Q S_total : ℝ}
    (hT : 0 < kB_T) (hσ : 0 < sigma_Q)
    (hfloor : johnsonNyquistPSD kB_T sigma_Q ≤ S_total) :
    0 < johnsonNyquistPSD kB_T sigma_Q ∧ 0 < S_total := by
  have hpos := johnsonNyquistPSD_pos kB_T sigma_Q hT hσ
  exact ⟨hpos, lt_of_lt_of_le hpos hfloor⟩

/-- **Worked detector operating point.** A linear detector measuring an analog-Hawking signal sees
total noise = Johnson–Nyquist thermal floor + Hawking excess, which *strictly* exceeds the thermal
floor (the excess is strictly positive). -/
theorem fdt_noise_floor_detector {kB_T sigma_Q hbar_omega greybody n_H : ℝ}
    (hσ : 0 < sigma_Q) (hω : 0 < hbar_omega) (hg : 0 < greybody) (hn : 0 < n_H) :
    johnsonNyquistPSD kB_T sigma_Q
      < johnsonNyquistPSD kB_T sigma_Q + hawkingNoisePSD hbar_omega sigma_Q greybody n_H := by
  have := hawkingNoisePSD_pos hbar_omega sigma_Q greybody n_H hω hσ hg hn
  linarith

/-- **Worked amplifier operating point (quantum limit).** A phase-insensitive linear amplifier adds
at least a half-quantum of noise (Caves' bound `A ≥ ℏω/2 > 0`), so its total output noise sits
strictly above the thermal floor, by at least one half-quantum. -/
theorem fdt_noise_floor_amplifier {kB_T sigma_Q hbar_omega addedNoise : ℝ}
    (hω : 0 < hbar_omega) (hcaves : hbar_omega / 2 ≤ addedNoise) :
    johnsonNyquistPSD kB_T sigma_Q < johnsonNyquistPSD kB_T sigma_Q + hbar_omega / 2
      ∧ johnsonNyquistPSD kB_T sigma_Q + hbar_omega / 2
          ≤ johnsonNyquistPSD kB_T sigma_Q + addedNoise :=
  ⟨by linarith, by linarith⟩

/-! ## Rare-event tail: linear-response large-deviation rate function -/

/-- **FDT-pinned mean noise current.** The linear-response rate function vanishes exactly at the
FDT-pinned mean noise current `W* = βσ²/2` — the most likely (typical) noise value. -/
theorem fdt_noise_current_mean (β σ_sq : ℝ) :
    linearResponseRateFunction β σ_sq (β * σ_sq / 2) = 0 := by
  simp [linearResponseRateFunction]

/-- **Rare-event tail bound.** For positive noise variance, the large-deviation rate function is
strictly positive at every noise current `W` away from the FDT-pinned mean `βσ²/2`. Since the
empirical noise current obeys `P(W) ∼ e^{−N·I(W)}`, every deviation from the FDT mean is
exponentially suppressed. -/
theorem fdt_rare_event_tail {β σ_sq W : ℝ} (hσ : 0 < σ_sq) (hW : W ≠ β * σ_sq / 2) :
    0 < linearResponseRateFunction β σ_sq W := by
  unfold linearResponseRateFunction
  have hne : W - β * σ_sq / 2 ≠ 0 := sub_ne_zero.mpr hW
  exact div_pos (by positivity) (by positivity)

/-- **Gallavotti–Cohen / W-form fluctuation theorem for the noise current.** The rate function's
forward/reverse asymmetry is `I(W) − I(−W) = −β W` — the entropy-production fluctuation relation that
governs the ratio of rare-event tails. (Re-export of the shipped linear-response GC symmetry.) -/
theorem fdt_gallavotti_cohen {β σ_sq : ℝ} (hσ : σ_sq ≠ 0) :
    WFormGallavottiCohen β (linearResponseRateFunction β σ_sq) :=
  linearResponseRateFunction_satisfies_WFormGC β σ_sq hσ

end SKEFTHawking.QuantumNetwork
